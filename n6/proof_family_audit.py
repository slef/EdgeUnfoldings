"""Exact example outside the three new simple sufficient theorem conditions.

An uncovered example is not a counterexample to unfolding. Its selected net
is checked separately; these tests explain the limits of the new criteria.
"""
import json
from pathlib import Path
from n6.polycert import Geometry
from n6.convex_patches import classify,geometry_patches
from n6.curvature import angle_product,interval_angle_le
from n6.curvature_pair import weighted_curvature_bound
from n6.intervals import I,norm2
from n6.certify import require


def verify(spec):
    g=Geometry(spec);patch=classify(spec)
    require(len(patch['nonconvex_patches'])>=2,'The zero/one-patch theorem already applies')
    products={v:angle_product(g.p,g.faces,g.h,v) for v in range(6)}
    records=[]
    for w in range(6):
        nxt={}
        for f in g.faces:
            if w in f:
                i=f.index(w);nxt[f[(i+1)%3]]=f[(i+2)%3]
        require(len(nxt)==4,'Expected four neighbors')
        ring=[min(nxt)]
        while len(ring)<4:ring.append(nxt[ring[-1]])
        v=next(x for x in range(6) if x!=w and x not in ring)
        high=interval_angle_le(products[w],(I(-1),-I(3).sqrt()))
        require(high is not None,'Curvature threshold unresolved')
        row=dict(sector_vertex=w,source=v,curvature_at_least_120=high)
        if high:
            weighted=weighted_curvature_bound(products[w],products[v])
            require(weighted is False,'Weighted curvature criterion may apply')
            row['weighted_curvature_bound']=False
            P=geometry_patches(g,dict(apex=v,antipode=w,equator=ring))
            diagonal2=norm2(g.vector(w,v));obstruction=None
            for p in P:
                if p['corner_relations_to_pi']!=['<','<']:continue
                gaps={u:norm2(g.vector(w,u))-diagonal2 for u in p['equator_edge']}
                if all(gap.lo>0 for gap in gaps.values()):
                    obstruction=dict(equator_edge=p['equator_edge'],patch_strictly_convex=True,
                                     squared_spoke_excesses={str(u):gap.pair() for u,gap in gaps.items()})
                    break
            require(obstruction is not None,'Short-edge cover may apply')
            row['short_edge_cover_obstruction']=obstruction
        records.append(row)
    return dict(result='verified_outside_three_new_simple_criteria',sharpest_apex=spec['selection']['apex'],
                sharpest_patch_classification=patch,vertices=records,
                scope='These exact coordinates satisfy none of the zero/one-patch, curvature-pair, or chord-based short-edge-cover criteria. The chosen unfolding is checked separately and can be successful. This is not an unfolding counterexample or a proof that a broader sector criterion fails.')


if __name__=='__main__':
    import argparse
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('certificate',type=Path)
    args=ap.parse_args();spec=json.loads(args.certificate.read_text());set_precision(spec.get('suggested_fractional_bits',192))
    print(json.dumps(verify(spec),indent=2))
