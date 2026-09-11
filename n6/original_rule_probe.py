"""Numerical diagnostics for original-edge rules; never proof premises.

The two candidate families already existed. This probe classifies why the
curvature proof accepts or rejects each tree before inspecting actual nets.
Affine and projective maps preserve the seed's polygonal faces. The sample
is finite, biased, and tolerance-dependent; unresolved cases are retained.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import time
import numpy as np
from n6.families import MINUS_FACES, PRISM_FACES
from n6.flat_octahedron import original_candidates
from n6.minus_patterns import TreeBatch
from n6.original_star_probe import apex_curvature
from n6.original_edge_rule import ring_for
from n6.trees import tree_data


SEEDS = {
    'minus': [[0,0,0],[20,20,0],[20,0,0],[0,20,0],[15,5,-20],[5,15,-20]],
    'prism': [[20,0,0],[0,20,0],[0,0,0],[24,0,20],[0,20,20],[0,0,20]],
}


def curvature_conditions(k, tree, ring):
    """Real-number sufficient predicates derived in ORIGINAL_EDGE_RULE.md.

    This floating implementation is for exploration only. Its numerical
    classification does not verify any premise of a mathematical proof.
    """
    v,w,c = (tree[x] for x in ('source','fan','slit'))
    a,d,b = ring[1:]
    old = min(max(k[v]-np.pi, np.pi-max(k)), 2*k[c]+k[w]-np.pi)
    new = min(np.pi-k[w], 2*k[c]+k[w]-np.pi,
              k[a]+k[c]+2*k[w]-np.pi, k[b]+k[c]+2*k[w]-np.pi,
              k[v]+k[a]+k[d]-np.pi, k[v]+k[d]+k[b]-np.pi,
              k[c]+k[w]+k[v]/2-np.pi)
    return float(old), float(new)


def sample(rng, seed):
    # Exact rational coordinates are recoverable from the saved integers.
    direction = rng.integers(-20,21,3)
    heights = seed @ direction
    gap = int(rng.choice([1,2,5,10,50,200,1000,10000]))
    denominators = heights-heights.min()+gap
    matrix = rng.integers(-30,31,(3,3))
    if np.linalg.det(matrix) <= .5:return None
    matrix = np.diag(rng.choice([1,3,10,30,100],3)) @ matrix
    numerators = seed @ matrix.T
    p = numerators/denominators[:,None]
    p -= p[0]
    p /= np.max(np.linalg.norm(p[:,None]-p[None],axis=2))
    return p, dict(numerators=numerators.tolist(),denominators=denominators.tolist())


def run(kind, samples, seed, seconds):
    faces = MINUS_FACES if kind=='minus' else PRISM_FACES
    family, trees = original_candidates(faces)
    rings = [ring_for(family,t['source'],t['fan'],t['slit']) for t in trees]
    batch = TreeBatch([tree_data(faces,t['cuts']) for t in trees],faces)
    rng=np.random.default_rng(seed); start=time.monotonic();counts=Counter();examples={}
    attempts=0; tol=1e-8
    while counts['samples']<samples and time.monotonic()-start<seconds:
        attempts+=1; proposal=sample(rng,np.array(SEEDS[kind],dtype=np.int64))
        if proposal is None:continue
        p,exact=proposal
        if any(np.linalg.norm(np.cross(p[f[1]]-p[f[0]],p[f[2]]-p[f[0]]))<1e-12 for f in faces):continue
        k=np.array([apex_curvature(p,faces,x) for x in range(6)])
        if min(k)<=tol or max(k)>=2*np.pi-tol:continue
        counts['samples']+=1
        values=np.array([curvature_conditions(k,t,r) for t,r in zip(trees,rings)])
        old=float(max(values[:,0]));new=float(max(values[:,1])); category='old' if old>tol else 'extended' if new>tol else 'unresolved'
        counts[category]+=1
        if category=='old':continue
        margins=batch.margins(p)
        best=float(max(margins))
        accepted=np.flatnonzero(values[:,1]>tol)
        counts['extended_accepted_trees_checked']+=len(accepted)
        failed=[int(i) for i in accepted if margins[i]<-tol]
        counts['extended_predicate_overlap_samples']+=bool(failed)
        if failed:
            examples['extended_predicate_failure']=dict(**exact,failed_trees=failed,
                curvature_degrees=(k*180/np.pi).tolist(),net_margins=margins.tolist())
        counts['original_family_failure' if best < -tol else 'original_family_safe_sample' if best>tol else 'original_family_numerically_unresolved']+=1
        if category not in examples or best<examples[category]['best_net_margin']:
            examples[category]=dict(**exact,curvature_degrees=(k*180/np.pi).tolist(),
                old_best=old,extended_best=new,best_net_margin=best,net_margins=margins.tolist(),
                extended_tree=int(np.argmax(values[:,1])),best_net_tree=int(np.argmax(margins)))
        if category=='unresolved':
            high=tuple(x for x in range(6) if k[x]>np.pi+tol)
            counts['unresolved_high_'+','.join(map(str,high))]+=1
            v=max({t['source'] for t in trees},key=lambda x:k[x])
            selected=max((i for i,t in enumerate(trees) if t['source']==v),key=lambda i:k[trees[i]['slit']])
            if margins[selected]<-tol:
                counts['sharper_original_source_allowed_maximum_failure']+=1
                key='selected_failure'
                if key not in examples or margins[selected]<examples[key]['selected_margin']:
                    examples[key]=dict(**exact,curvature_degrees=(k*180/np.pi).tolist(),
                        selected_tree=selected,selected_margin=float(margins[selected]),
                        best_net_tree=int(np.argmax(margins)),net_margins=margins.tolist(),
                        old_best=old,extended_best=new)
    return dict(scope='Numerical exploration only. Failed proof predicates are not overlaps; samples are not coverage.',
        kind=kind,seed=seed,attempts=attempts,seconds=time.monotonic()-start,tolerance=tol,
        counts=dict(counts),trees=trees,rings=rings,examples=examples)


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('kind',choices=SEEDS)
    ap.add_argument('--samples',type=int,default=3000);ap.add_argument('--seed',type=int,default=6091201)
    ap.add_argument('--seconds',type=float,default=45);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();report=run(args.kind,args.samples,args.seed,args.seconds)
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report['counts'],indent=2))
