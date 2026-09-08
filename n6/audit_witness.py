"""Exact check of a counterexample to the unqualified D half-plane lemma.

This refutes a supporting statement, not unfoldability or Case A.
"""
import json
from pathlib import Path
from n6.certify import Geometry, require, tree_path
from n6.intervals import sub, det


def verify_witness(spec):
    g = Geometry(spec)
    w = spec['halfplane_claim']
    a,b,v,u,far = (w[k] for k in ('petal','middle_petal','apex','shared_equator','far_equator'))
    require(set(g.faces[a]) == {v,u,far}, 'Wrong petal labels')
    require({v,u} <= set(g.faces[b]), 'Wrong middle-petal labels')
    path = tree_path(g.adj,a,b)
    require(all(u in g.faces[f] for f in path), 'Equator copies not joined')
    require(any(v not in g.faces[f] for f in path), 'Apex copies not separated')
    A = g.develop([a]); B = g.develop(path)
    d = sub(A[v], A[u])
    side_far = det(d, sub(A[far], A[u]))
    side_middle = det(d, sub(B[v], A[u]))
    require(side_far.lo > 0 and side_middle.lo > 0 or side_far.hi < 0 and side_middle.hi < 0,
            'Same strict side is not certified')
    return {'result':'verified_counterexample_to_unqualified_halfplane_claim',
            'side_far':side_far.pair(), 'side_middle_apex':side_middle.pair(),
            'scope':'Exact convex integer-coordinate octahedron; no curvature ranking is asserted by this checker. Not a counterexample to Durer.'}


if __name__ == '__main__':
    spec = json.loads(Path('n6/results/d-lemma-counterexample.json').read_text())
    print(json.dumps(verify_witness(spec),indent=2))
