"""Numerical differential validation on every six-vertex combinatorial type.

The archived polynomial predicate is compared with polygon clipping after
Claude's independent rigid-motion development. These tests are not proofs.
"""
import itertools
from fractions import Fraction
import json
from pathlib import Path
import sys
import networkx as nx
import numpy as np
from n6.encoding import Counterexample, dual_trees, graph6, tree_paths
from n6.archive_validation import numeric_model, evaluate, clipped_area

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'durer_small_n'))
from unfold2 import poly_faces, local_coords, dual_edges, unfold
from octa import Octa, octa_structure
from n6.sector_probe import setup, net, overlap


def fixtures():
    yield 'prism', np.array([(0,0,0),(4,0,0),(1,3,0),(1,1,5),(5,1,5),(2,4,5)],float)
    yield 'pentagonal pyramid', np.array([(0,0,4),(-3,-2,0),(2,-3,0),(4,0,0),(1,4,0),(-3,3,0)],float)
    a,b,c,cp=np.array([(0,0,0),(1.3,.1,0),(.5,1.1,0),(.6,.9,1.2)])
    yield 'prism with diagonal',np.array([a,b,c,c+(a-c)+1.05*(cp-c),c+.9*(b-c)+.95*(cp-c),cp])
    yield 'degree 5,4,4,3,3,3',np.array([(0,.1,1.2),(1.3,0,.15),(.3,1,0),(-.8,.6,0),(-.8,-.6,0),(.3,-1,0)])
    yield 'octahedron minus edge',np.array([(0,0,1),(.05,0,-1.1),(1,0,.1),(-1,0,-.1),(.35,.95,0),(-.3,1,.05)])
    t=np.array([(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)],float)
    yield 'stacked simplicial',np.vstack([t,[.6,-.6,.6],[-.6,.6,.6]])
    cert=json.loads((ROOT/'n6/results/octahedron-box.certificate.json').read_text())
    yield 'octahedron',np.array([[(float(Fraction(q[0]))+float(Fraction(q[1])))/2 for q in pt] for pt in cert['coordinate_box']])


def normalize(p,ce):
    a,b,c=ce.faces[0][:3]; origin=p[a].copy()
    ex=p[b]-origin;scale=np.linalg.norm(ex);ex/=scale
    ey=p[c]-origin;ey-=ey@ex*ex;ey/=np.linalg.norm(ey)
    ez=np.cross(ex,ey)
    other=next(v for v in ce.g if v not in ce.faces[0])
    if (p[other]-origin)@ez>0:ez=-ez
    return (p-origin)@np.array([ex,ey,ez]).T/scale


def run():
    records=[];types=set()
    for name,p in fixtures():
        fs=poly_faces(p);g=nx.Graph();g.add_nodes_from(range(6))
        for f in fs:g.add_edges_from(zip(f,f[1:]+f[:1]))
        typ=(tuple(sorted(dict(g.degree()).values())),tuple(sorted(map(len,fs))))
        if typ in types:raise AssertionError('Duplicate fixture type')
        types.add(typ)
        ce=Counterexample(g);p=normalize(p,ce);vals=numeric_model(ce,p)
        # Use the source's face orientations, original polygonal facets intact.
        L=local_coords(p,ce.faces);E=dual_edges(ce.faces)
        lookup={frozenset((a,b)):i for i,(a,b,_,_) in enumerate(E)}
        memo={};path_memo={};tested=bad=0
        def path_overlaps(path):
            path=tuple(path)
            if path in path_memo:return path_memo[path]
            A,da=ce.develop(path[:1]);B,db=ce.develop(path)
            # Remove positive homogeneous factors before numerical signs.
            # Direct floating evaluation of expanded high-degree determinants
            # can turn exact boundary contacts into enormous cancellation errors.
            a,b=ce.faces[path[0]][:2];scale=np.linalg.norm(p[b]-p[a])
            def points(q,d,f):
                denominator=evaluate(d,vals,memo)*scale
                return np.array([[evaluate(x,vals,memo)/denominator for x in q[v]] for v in f])
            pa=points(A,da,ce.faces[path[0]]);pb=points(B,db,ce.faces[path[-1]])
            tests=[]
            for X,Y in [(pa,pb),(pb,pa)]:
                for u,v in zip(X,np.roll(X,-1,axis=0)):
                    e=v-u
                    tests.append(max(e[0]*(q-u)[1]-e[1]*(q-u)[0] for q in Y)>1e-9)
            path_memo[path]=all(tests)
            return path_memo[path]
        for t in dual_trees(g,ce.dual):
            encoded=any(path_overlaps(path) for path in tree_paths(t))
            placed=unfold(ce.faces,L,E,[lookup[frozenset(e)] for e in t.edges()])
            polygons=[np.array([q[v] for v in f]) for f,q in zip(ce.faces,placed)]
            area=max(clipped_area(A,B) for A,B in itertools.combinations(polygons,2))
            reference=area>1e-9
            if encoded != reference:
                raise AssertionError((name,sorted(t.edges()),encoded,area))
            tested+=1;bad+=int(reference)
        records.append(dict(case=name,graph6=graph6(g),degrees=typ[0],facet_sizes=typ[1],trees=tested,overlapping=bad))
    # Direct comparison of all 24 archive nets with Claude's named nets.
    p=dict(fixtures())['octahedron'];fs,plans=setup(p)
    for v,w,u,plan in plans:
        o=Octa(p,v);k=o.u.index(u)
        if overlap(net(p,fs,plan)) != bool(o.overlaps(k)):
            raise AssertionError(('octahedron implementations disagree',v,w,u))
    return {'scope':'Numerical implementation validation only; not universal coverage.',
            'six_vertex_types':len(types),'trees':sum(r['trees'] for r in records),
            'predicate_evaluation':'Remove positive homogeneous factors before floating-point sign tests; raw expanded floating evaluation is unstable at contacts.',
            'archive_vs_claude_octahedron_nets':len(plans),'cases':records}


if __name__=='__main__':
    result=run()
    (ROOT/'n6/results/differential-validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
