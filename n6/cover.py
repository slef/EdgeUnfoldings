"""Generate and independently replay an exact binary subdivision cover.

Every leaf contains a complete original-facet unfolding certificate. The binary
splits cover the entire stated closed root box, including their common borders.
Unresolved leaves remain explicit and prevent a complete-cover verdict. The
finite root box is not asserted to cover the space of convex six-vertex shapes.
"""
from __future__ import annotations
import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction as F
import json
import gzip
from pathlib import Path
import time
from n6.certify import require
from n6.polycert import Geometry,PairUnresolved,propose_pairs,verify as verify_leaf


def read_cover(path):
    raw=path.read_bytes()
    if path.suffix=='.gz':raw=gzip.decompress(raw)
    return json.loads(raw)


def write_cover(path,data):
    # Deeply indented binary trees can be much larger than their mathematical
    # content. Compact JSON, optionally gzipped, preserves every exact witness.
    raw=(json.dumps(data,separators=(',',':'))+'\n').encode()
    if path.suffix=='.gz':raw=gzip.compress(raw,mtime=0)
    temp=path.with_suffix('.tmp');temp.write_bytes(raw);temp.replace(path)


def children_boxes(box,axis,value):
    require(isinstance(axis,int) and 0<=axis<len(box),'Invalid split axis')
    require(not isinstance(value,float),'Split must be rational, not floating point')
    mid=F(value);lo,hi=map(F,box[axis]);require(lo<mid<hi,'Split is not strictly interior')
    left,right=deepcopy(box),deepcopy(box)
    left[axis]=[str(lo),str(mid)];right[axis]=[str(mid),str(hi)]
    return left,right


def leaf_spec(base,box,node):
    return {**base,'parameter_box':box,'cut_edges':node['cuts'],'pair_witnesses':node['pairs']}


def leaves(cover):
    """Yield (node, implied box, depth), validating every subdivision."""
    require(cover.get('schema')=='n6-binary-region-cover-v1','Unknown cover schema')
    base=cover['geometry'];box=base['parameter_box']
    require(all(len(q)==2 and all(not isinstance(x,float) for x in q) and F(q[0])<=F(q[1]) for q in box),'Invalid root box')
    stack=[(cover['tree'],box,0)]
    while stack:
        node,box,depth=stack.pop();kind=node['kind']
        if kind=='split':
            require(len(node['children'])==2,'Split must have exactly two children')
            left,right=children_boxes(box,node['axis'],node['value'])
            stack.extend([(node['children'][1],right,depth+1),(node['children'][0],left,depth+1)])
        else:
            require(kind in ('certified','unresolved'),'Unknown leaf kind')
            yield node,box,depth


def verify(cover):
    counts=Counter();trees=set();deepest=0;dimension=len(cover['geometry']['parameter_box'])
    for node,box,depth in leaves(cover):
        require(node['kind']=='certified','Unresolved region: cover is incomplete')
        report=verify_leaf(leaf_spec(cover['geometry'],box,node))
        require(report['result']=='verified','Leaf certificate failed')
        counts.update(report['pairs']);counts['leaves']+=1;deepest=max(deepest,depth)
        trees.add(tuple(sorted(tuple(e) for e in node['cuts'])))
    require(counts['leaves']>0,'Empty cover')
    return dict(result='verified_complete_region_cover',parameter_dimension=dimension,
                leaves=counts.pop('leaves'),distinct_cut_trees=len(trees),maximum_depth=deepest,
                checked_face_pairs=dict(counts),
                scope='Every tuple in this explicit closed root box; no claim of global metric-space coverage',
                coverage_argument='Every split has exactly two closed children [lo,split] and [split,hi]; every leaf is verified.')


def summary(cover):
    counts=Counter();depth=0;volumes=Counter()
    widths=[F(b)-F(a) for a,b in cover['geometry']['parameter_box']]
    for node,box,d in leaves(cover):
        counts[node['kind']]+=1;depth=max(depth,d);fraction=F(1)
        for (a,b),width in zip(box,widths):
            if width:fraction*=(F(b)-F(a))/width
        volumes[node['kind']]+=fraction
    require(sum(volumes.values())==1,'Subdivision volume does not equal the root')
    return dict(counts,maximum_depth=depth,
                parameter_volume_fractions={k:str(v) for k,v in volumes.items()},
                scope='Structural bookkeeping only; certified labels are not independently replayed here. Volume is in these chart parameters.')


def merge_covers(covers):
    """Overlay closed subdivisions, using any certificate that covers a cell.

    The output is a candidate cover requiring independent replay. Restricting
    a certified leaf preserves its mathematical witness, but interval replay
    may still be inconclusive and must never be skipped.
    """
    require(bool(covers),'No input covers')
    base=covers[0]['geometry']
    for cover in covers:
        require(cover['geometry']==base,'Cannot merge different root geometries')
        list(leaves(cover))  # Validate all split positions before using them.
    def trim(node,box):
        while node['kind']=='split':
            lo,hi=map(F,box[node['axis']]);mid=F(node['value'])
            if hi<=mid:node=node['children'][0]
            elif lo>=mid:node=node['children'][1]
            else:break
        return node
    def combine(nodes,box):
        nodes=[trim(n,box) for n in nodes]
        certified=next((n for n in nodes if n['kind']=='certified'),None)
        if certified is not None:return deepcopy(certified)
        split=next((n for n in nodes if n['kind']=='split'),None)
        if split is None:return dict(kind='unresolved',reason='Unresolved in every input cover')
        children=children_boxes(box,split['axis'],split['value'])
        return dict(kind='split',axis=split['axis'],value=split['value'],
                    children=[combine(nodes,b) for b in children])
    return dict(schema='n6-binary-region-cover-v1',geometry=deepcopy(base),
                tree=combine([c['tree'] for c in covers],base['parameter_box']),
                merging=dict(inputs=len(covers),scope='Candidate union; every resulting leaf still requires independent geometric replay.'))


def affine_split_hint(g,pair):
    """Heuristic only: split a parameter contributing to a failed separator.

    Score the closest separating-edge enclosure by its relative excess above
    zero, then use the largest retained affine coefficient. Nonlinear error can
    defeat this heuristic; every proposed child still needs exact verification.
    """
    a,b=pair;best=None
    for owner in (a,b):
        f=g.faces[owner]
        for edge in zip(f,f[1:]+f[:1]):
            bounds=g.separating_bounds(a,b,owner,edge)
            scored=[(q.hi/(q.hi-q.lo),q) for q in bounds if q.hi>0 and q.hi>q.lo and getattr(q,'a',{})]
            if not scored:continue
            score,q=max(scored,key=lambda x:x[0])
            axis=max(q.a,key=lambda j:abs(q.a[j]))
            if best is None or score<best[0]:best=(score,axis)
    return best


def rank_trees(base,box,trees):
    """Floating proposals only. Neither ranking nor margins enter verification."""
    import numpy as np
    from n6.prism_diagonal import develop,pair_score
    center=[float((F(a)+F(b))/2) for a,b in box]
    def evaluate(terms):return sum(float(F(c))*np.prod([x**k for x,k in zip(center,e)]) for c,e in terms)
    P=np.array([[evaluate(q) for q in p] for p in base['coordinate_polynomials']])
    faces=[tuple(f) for f in base['faces']];ranking=[]
    for index,t in enumerate(trees):
        net=develop(P,faces,t['hinges'],root=0)
        margin=min((-pair_score(net[a],net[b]) for a,b in t['pairs']),default=float('inf'))
        if np.isfinite(margin) or margin==float('inf'):ranking.append((margin,index))
    return [trees[i] for _,i in sorted(ranking,reverse=True)]


def generate(base,output,max_seconds=300,max_leaves=10000,max_depth=40,candidates=3,resume=None,split_strategy='width',candidate_trees=None):
    from n6.trees import all_trees
    start=time.monotonic();trees=all_trees([tuple(f) for f in base['faces']]) if candidate_trees is None else candidate_trees
    require(bool(trees),'Empty candidate tree family')
    cover=deepcopy(resume) if resume is not None else dict(schema='n6-binary-region-cover-v1',geometry=base,tree=dict(kind='unresolved',reason='pending'))
    require(cover['geometry']==base,'Resume geometry differs from input')
    initial_widths=[F(b)-F(a) for a,b in base['parameter_box']]
    pending=[x for x in leaves(cover) if x[0]['kind']=='unresolved'];leaf_count=sum(1 for _ in leaves(cover))
    attempts=successes=splits=0;failures=Counter();saved=start
    while pending and time.monotonic()-start<max_seconds:
        node,box,depth=pending.pop();attempts+=1;cert=None;reason='no candidate tree';hint=None
        # A failed interval estimate is never accepted as proof of infeasibility.
        try:
            # Facet checks, polynomial projections, and path developments can
            # be reused while trying different trees for the same region.
            g=Geometry({**base,'parameter_box':box,'cut_edges':trees[0]['cuts']})
            for t in rank_trees(base,box,trees)[:candidates]:
                g.adj={i:[] for i in range(len(g.faces))}
                for a,b in t['hinges']:g.adj[a].append(b);g.adj[b].append(a)
                try:
                    pairs=propose_pairs(g)
                    cert={**base,'parameter_box':box,'cut_edges':t['cuts'],'pair_witnesses':pairs}
                    break
                except ValueError as error:
                    reason=str(error)
                    if split_strategy=='affine' and isinstance(error,PairUnresolved):
                        suggestion=affine_split_hint(g,error.faces)
                        if suggestion is not None and (hint is None or suggestion[0]<hint[0]):hint=suggestion
        except ValueError as error:reason=str(error)
        if cert is not None:
            node.clear();node.update(kind='certified',cuts=cert['cut_edges'],pairs=cert['pair_witnesses']);successes+=1
        else:
            failures[reason]+=1;node['reason']=reason
            if depth<max_depth and leaf_count<max_leaves:
                ratios=[(F(b)-F(a))/width if width else F(0) for (a,b),width in zip(box,initial_widths)]
                axis=max(range(len(box)),key=ratios.__getitem__) if box else None
                if hint is not None and ratios[hint[1]]>0:axis=hint[1]
                if axis is not None and ratios[axis]>0:
                    mid=(F(box[axis][0])+F(box[axis][1]))/2
                    boxes=children_boxes(box,axis,mid);kids=[dict(kind='unresolved',reason='pending') for _ in range(2)]
                    node.clear();node.update(kind='split',axis=axis,value=str(mid),children=kids)
                    pending.extend((kid,b,depth+1) for kid,b in reversed(list(zip(kids,boxes))))
                    splits+=1;leaf_count+=1
        if time.monotonic()-saved>=5:
            cover['generation'] = dict(seconds=time.monotonic()-start,attempts=attempts,successes=successes,splits=splits,failures=dict(failures),summary=summary(cover))
            write_cover(output,cover);saved=time.monotonic()
            print(json.dumps(cover['generation']),flush=True)
    cover['generation']=dict(seconds=time.monotonic()-start,attempts=attempts,successes=successes,splits=splits,failures=dict(failures),summary=summary(cover),
                             split_strategy=split_strategy,
                             scope='Generation statistics only; replay the cover verifier for a proof verdict')
    write_cover(output,cover)
    return cover


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('action',choices=['generate','verify','summary','merge'])
    ap.add_argument('input',type=Path);ap.add_argument('--output',type=Path)
    ap.add_argument('--seconds',type=float,default=300);ap.add_argument('--max-leaves',type=int,default=10000)
    ap.add_argument('--max-depth',type=int,default=40);ap.add_argument('--candidates',type=int,default=3);ap.add_argument('--resume',action='store_true')
    ap.add_argument('--split-strategy',choices=['width','affine'],default='width')
    ap.add_argument('--with-cover',action='append',type=Path,default=[])
    args=ap.parse_args();data=read_cover(args.input)
    if args.action=='verify':print(json.dumps(verify(data),indent=2));return
    if args.action=='summary':print(json.dumps(summary(data),indent=2));return
    if args.output is None:ap.error('--output required')
    if args.action=='merge':
        if not args.with_cover:ap.error('--with-cover required for merge')
        result=merge_covers([data]+[read_cover(p) for p in args.with_cover]);write_cover(args.output,result)
        print(json.dumps(summary(result),indent=2));return
    if min(args.seconds,args.max_leaves,args.max_depth,args.candidates)<=0:ap.error('Limits must be positive')
    resume=read_cover(args.output) if args.resume else None
    result=generate(data,args.output,args.seconds,args.max_leaves,args.max_depth,args.candidates,resume,args.split_strategy)
    print(json.dumps(result['generation'],indent=2))


if __name__=='__main__':main()
