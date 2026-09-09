"""Exact region and fixed-tree failure certificates for original polygonal facets.

No NumPy, solver, or floating arithmetic is used. Parameter polynomials establish
coplanarity as identities; outward rational intervals establish strict convexity
and planar separation/overlap. A region is not a global n=6 certificate.
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path
from n6.certify import Geometry as TriangleGeometry, require, edge, tree_path
from n6.intervals import I, sub, dot, norm2, cross, det
from n6.polynomials import Poly


def pdot(a,b):return sum(x*y for x,y in zip(a,b))


def axis_length(polynomials,bounds):
    """Exact norm shortcut when only one coordinate is identically nonzero.

    Its certified sign turns sqrt(q*q) into +/-q and retains correlations.
    Return None if a sign is unresolved or more than one coordinate is needed.
    """
    nonzero=[i for i,p in enumerate(polynomials) if not p.is_zero()]
    if len(nonzero)!=1:return None
    value=bounds[nonzero[0]]
    if value.lo>=0:return value
    if value.hi<=0:return -value
    return None


def point_spec(points,faces,cuts):
    return dict(schema='n6-polyhedron-region-v1',parameter_box=[],
                coordinate_polynomials=[[[[str(x),[]]] for x in p] for p in points],
                faces=[list(f) for f in faces],cut_edges=[list(e) for e in cuts])


class Geometry(TriangleGeometry):
    def __init__(self,spec):
        require(spec.get('schema')=='n6-polyhedron-region-v1','Unknown region schema')
        mode=spec.get('arithmetic_mode','interval')
        require(mode in ('interval','affine'),'Unknown arithmetic mode')
        if mode=='affine':
            from n6.affine import A
            self.box=[A.variable(*q,i) for i,q in enumerate(spec['parameter_box'])]
        else:self.box=[I(*q) for q in spec['parameter_box']]
        self.arithmetic_mode=mode;n=len(self.box)
        raw=spec['coordinate_polynomials']
        require(len(raw)==6 and all(len(p)==3 for p in raw),'Expected six 3D points')
        P=[tuple(Poly(n,q) for q in p) for p in raw]
        self.polynomial_points=P
        self.p=p=[tuple(q.evaluate(self.box) for q in pt) for pt in P]
        self.faces=fs=[tuple(f) for f in spec['faces']]
        require(len(set(map(frozenset,fs)))==len(fs),'Repeated facet')
        require(all(3<=len(f)<=6 and len(set(f))==len(f) and set(f)<=set(range(6)) for f in fs),'Invalid facet')
        inc={};directed=set()
        for i,f in enumerate(fs):
            for a,b in zip(f,f[1:]+f[:1]):
                require((a,b) not in directed,'Inconsistent facet orientation')
                directed.add((a,b));inc.setdefault(edge(a,b),[]).append(i)
        require(all(len(owners)==2 for owners in inc.values()),'Surface is not closed')
        require(all((b,a) in directed for a,b in directed),'Unpaired oriented edge')
        require(6-len(inc)+len(fs)==2,'Wrong Euler characteristic')
        for v in range(6):
            # The link at every vertex must be one simple cycle.
            link={}
            for f in fs:
                if v not in f:continue
                k=f.index(v);a,b=f[k-1],f[(k+1)%len(f)]
                link.setdefault(a,[]).append(b);link.setdefault(b,[]).append(a)
            require(len(link)>=3 and all(len(vs)==2 for vs in link.values()),'Invalid vertex link')
            for w in link:tree_path(link,next(iter(link)),w)
        self.h=[];self.N=[];self.support_bounds=[];self.planarity_identities=0
        for f in fs:
            a,b,c=f[:3]
            Npoly=cross(sub(P[b],P[a]),sub(P[c],P[a]))
            N=tuple(q.evaluate(self.box) for q in Npoly)
            h2=norm2(N)
            require(h2.lo>0,'Cannot certify positive facet area')
            self.N.append(N)
            length=axis_length(Npoly,N)
            self.h.append(h2.sqrt() if length is None else length)
            for v in range(6):
                support=pdot(Npoly,sub(P[v],P[a]))
                if v in f:
                    require(support.is_zero(),'Facet coplanarity is not a polynomial identity')
                    self.planarity_identities+=1
                else:
                    bound=support.evaluate(self.box)
                    require(bound.hi<0,'Cannot certify strict facet support')
                    self.support_bounds.append(bound)
            # A nondegenerate triangle is already strictly convex. Re-expanding
            # N dot N as a polynomial here needlessly loses its positive-square
            # structure in interval evaluation.
            if len(f)==3:continue
            for u,v in zip(f,f[1:]+f[:1]):
                for w in f:
                    if w in (u,v):continue
                    turn=pdot(Npoly,cross(sub(P[v],P[u]),sub(P[w],P[u])))
                    require(turn.evaluate(self.box).lo>0,'Cannot certify ordered convex facet')
        cuts_raw=spec['cut_edges'];cuts={edge(*e) for e in cuts_raw}
        require(len(cuts)==len(cuts_raw)==5 and cuts<=set(inc),'Invalid cut set')
        cadj={v:[] for v in range(6)}
        for a,b in cuts:cadj[a].append(b);cadj[b].append(a)
        for v in range(6):tree_path(cadj,0,v)
        self.adj=adj={i:[] for i in range(len(fs))}
        for e,(a,b) in inc.items():
            if e not in cuts:adj[a].append(b);adj[b].append(a)
        require(sum(map(len,adj.values()))==2*(len(fs)-1),'Wrong hinge count')
        for f in adj:tree_path(adj,0,f)
        self.cache={};self.vector_cache={};self.projection_cache={}

    def vector(self,a,b):
        key=(a,b)
        if key not in self.vector_cache:
            self.vector_cache[key]=tuple(q.evaluate(self.box) for q in sub(self.polynomial_points[b],self.polynomial_points[a]))
        return self.vector_cache[key]

    def projection(self,a,b,v):
        """Dot projection and positive oriented cross length along facet edge.

        All other vertices of an ordered convex facet are strictly to the left
        of its oriented edge. Thus the signed in-plane cross length equals the
        positive square root of the squared 3D cross length. Planarity eliminates
        the need to divide by a second, interval-valued facet normal length.
        """
        key=(a,b,v)
        if key not in self.projection_cache:
            P=self.polynomial_points;e=sub(P[b],P[a]);t=sub(P[v],P[a])
            d=pdot(e,t).evaluate(self.box)
            cross_polynomials=cross(e,t)
            cross_bounds=tuple(q.evaluate(self.box) for q in cross_polynomials)
            height=axis_length(cross_polynomials,cross_bounds)
            if height is None:height=norm2(cross_bounds).sqrt()
            self.projection_cache[key]=(d,height)
        return self.projection_cache[key]

    def develop(self,path):
        path=tuple(path)
        if path in self.cache:return self.cache[path]
        f=self.faces[path[-1]]
        if len(path)==1:
            a,b=f[:2];e=self.vector(a,b);ell=norm2(e).sqrt()
            q={a:(I(0),I(0)),b:(ell,I(0))}
            for v in f:
                if v in (a,b):continue
                d,height=self.projection(a,b,v);q[v]=(d/ell,height/ell)
        else:
            require(path[-1] in self.adj[path[-2]],'Path uses a cut edge')
            old=self.develop(path[:-1]);shared=set(f)&set(self.faces[path[-2]])
            a,b=next((a,b) for a,b in zip(f,f[1:]+f[:1]) if {a,b}==shared)
            e=self.vector(a,b);s=norm2(e)
            U=sub(old[b],old[a]);JU=(-U[1],U[0]);q={}
            for v in f:
                if v in shared:q[v]=old[v];continue
                d,height=self.projection(a,b,v)
                q[v]=tuple(old[a][j]+(d*U[j]+height*JU[j])/s for j in range(2))
        self.cache[path]=q
        return q


class PairUnresolved(ValueError):
    def __init__(self,a,b):
        self.faces=(a,b)
        super().__init__(f'Pair {(a,b)} unresolved; no certificate produced')


def propose_pairs(g):
    """Propose all pair witnesses for an already checked geometry and hinge tree.

    Generators may reuse geometry and path caches across candidate trees. The
    independent verifier always reconstructs the geometry and tree from input.
    """
    witnesses=[]
    for a,b in itertools.combinations(range(len(g.faces)),2):
        path=tree_path(g.adj,a,b)
        common=set.intersection(*(set(g.faces[f]) for f in path))
        if common:
            witnesses.append(dict(faces=[a,b],kind='vertex_fan',vertex=min(common)))
            continue
        if len(path)==3:
            # Pinciu (CCCG 2007), Theorem 1: the edge-neighborhood of a
            # face unfolds without overlap with every neighbor hinged to it.
            # The relative placement of these two faces is exactly that net.
            witnesses.append(dict(faces=[a,b],kind='face_neighborhood',base=path[1]))
            continue
        found=None
        for owner in (a,b):
            f=g.faces[owner]
            for e in zip(f,f[1:]+f[:1]):
                if all(q.hi<=0 for q in g.separating_bounds(a,b,owner,e)):
                    found=dict(faces=[a,b],kind='separating_edge',owner=owner,edge=list(e));break
            if found:break
        if found is None:raise PairUnresolved(a,b)
        witnesses.append(found)
    return witnesses


def make_certificate(spec):
    return {**spec,'pair_witnesses':propose_pairs(Geometry(spec))}


def verify(cert):
    from n6.intervals import BITS
    g=Geometry(cert);remaining=set(itertools.combinations(range(len(g.faces)),2))
    counts=dict(vertex_fan=0,separating_edge=0)
    for w in cert['pair_witnesses']:
        pair=tuple(w['faces']);require(pair in remaining,'Repeated or invalid pair')
        remaining.remove(pair);a,b=pair
        if w['kind']=='vertex_fan':
            path=tree_path(g.adj,a,b)
            require(all(w['vertex'] in g.faces[f] for f in path),'Not the same uncut vertex copy')
        elif w['kind']=='separating_edge':
            require(all(q.hi<=0 for q in g.separating_bounds(a,b,w['owner'],w['edge'])),'Invalid separator')
        elif w['kind']=='face_neighborhood':
            path=tree_path(g.adj,a,b)
            require(len(path)==3 and path[1]==w['base'],'Not two direct neighbors of the stated base face')
            counts.setdefault('face_neighborhood',0)
        else:raise ValueError('Unknown witness kind')
        counts[w['kind']]+=1
    require(not remaining,'Missing face pairs')
    report=dict(result='verified',scope='Every parameter tuple in the explicit region, not a universal n=6 theorem',
                parameter_dimension=len(g.box),facet_sizes=list(map(len,g.faces)),
                pairs=counts,strict_facet_supports=len(g.support_bounds),
                planarity_identities=g.planarity_identities,arithmetic='Exact rational polynomials and outward dyadic intervals',
                linear_correlations=g.arithmetic_mode=='affine',fractional_bits=BITS)
    if counts.get('face_neighborhood'):
        report['theorem_dependencies']=[dict(author='Val Pinciu',year=2007,theorem=1,
            title='On the Fewest Nets Problem for Convex Polyhedra',
            url='https://cccg.ca/proceedings/2007/01a4.pdf')]
    return report


def make_overlap(spec,a,b):
    g=Geometry(spec);_,A,B=g.pair_geometry(a,b);witnesses=[]
    for owner,X,Y in ((a,A,B),(b,B,A)):
        f=g.faces[owner]
        for u,v in zip(f,f[1:]+f[:1]):
            choices=[w for w in Y if det(sub(X[v],X[u]),sub(Y[w],X[u])).lo>0]
            require(bool(choices),'Overlap not certified')
            witnesses.append(dict(owner=owner,edge=[u,v],other_vertex=min(choices)))
    return {**spec,'overlap_witness':dict(faces=[a,b],edge_witnesses=witnesses)}


def verify_overlap(cert):
    g=Geometry(cert);w=cert['overlap_witness'];a,b=w['faces']
    require(isinstance(a,int) and isinstance(b,int) and 0<=a<b<len(g.faces),'Invalid overlap pair')
    _,A,B=g.pair_geometry(a,b)
    remaining={(owner,u,v) for owner in (a,b) for u,v in zip(g.faces[owner],g.faces[owner][1:]+g.faces[owner][:1])}
    margins=[]
    for item in w['edge_witnesses']:
        owner=item['owner'];u,v=item['edge'];key=(owner,u,v)
        require(key in remaining,'Repeated or invalid edge witness');remaining.remove(key)
        X,Y=(A,B) if owner==a else (B,A);other=item['other_vertex']
        require(other in Y,'Other point is not in other face')
        bound=det(sub(X[v],X[u]),sub(Y[other],X[u]))
        require(bound.lo>0,'Overlap sign not strictly certified');margins.append(str(bound.lo))
    require(not remaining,'Missing edge witnesses')
    return dict(result='verified_positive_area_overlap',faces=[a,b],strict_signs=len(margins),lower_bounds=margins,
                scope='Failure of this specified cut tree only; not a counterexample to edge unfoldability',
                facet_sizes=list(map(len,g.faces)),strict_facet_supports=len(g.support_bounds))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action',choices=['generate','verify','verify-overlap'])
    ap.add_argument('input',type=Path);ap.add_argument('--output',type=Path)
    ap.add_argument('--bits',type=int,default=80)
    args=ap.parse_args();spec=json.loads(args.input.read_text())
    from n6.intervals import set_precision
    set_precision(args.bits)
    if args.action=='generate':
        if args.output is None:ap.error('--output required')
        spec=make_certificate(spec);result=verify(spec)
        args.output.write_text(json.dumps(spec,indent=2)+'\n')
    else:result=(verify_overlap if args.action=='verify-overlap' else verify)(spec)
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
