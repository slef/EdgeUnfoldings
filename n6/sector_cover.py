"""Exact hypotheses for the short-edge cover sufficient unfolding theorem.

The written argument in OCTA_SHORT_EDGES.md depends on the exterior-sector
star-unfolding theorem. This is not a formal proof checker for that argument.
"""
import json
from pathlib import Path
from n6.polycert import Geometry
from n6.convex_patches import geometry_patches
from n6.curvature import angle_product,interval_angle_le
from n6.intervals import I,norm2
from n6.certify import require


def verify(spec):
    g=Geometry(spec);claim=spec['sector_cover']
    w,v,ring=claim['sector_vertex'],claim['source'],claim['equator']
    patches=geometry_patches(g,dict(apex=v,antipode=w,equator=ring))
    total=angle_product(g.p,g.faces,g.h,w)
    require(interval_angle_le(total,(I(-1),-I(3).sqrt())) is True,
            'Cannot certify sector-vertex curvature at least 2*pi/3')
    diagonal2=norm2(g.vector(w,v));gaps={u:diagonal2-norm2(g.vector(w,u)) for u in ring}
    short={u for u in ring if gaps[u].lo>=0}
    routes=[];choices=set()
    for patch in patches:
        # A straight corner puts the pole-to-pole diagonal through an equator
        # vertex. Such a path cannot be shortest at positive vertex curvature.
        valid=all(r=='<' for r in patch['corner_relations_to_pi'])
        endpoints=[u for u in patch['equator_edge'] if u in short]
        if valid:
            require(bool(endpoints),'A possible shortest-path patch has no certified short endpoint')
            choices.update(endpoints)
        routes.append(dict(patch=patch['index'],possible_shortest_path=valid,
                           short_endpoints=endpoints,corner_relations=patch['corner_relations_to_pi']))
    require(bool(choices),'No certified candidate: a strictly convex patch must exist')
    return dict(result='verified_short_edge_cover_hypotheses',source=v,sector_vertex=w,
                curvature_threshold='2*pi/3 (120 degrees)',angle_sum_product=[q.pair() for q in total],
                diagonal_squared=diagonal2.pair(),short_vertices=sorted(short),
                squared_length_gaps={str(u):gap.pair() for u,gap in gaps.items()},routes=routes,
                candidate_slit_vertices=sorted(choices),
                conclusion='At least one tree star(source) plus sector_vertex--u, for a listed u, is nonoverlapping. Choose a shortest two-face pole-to-pole path and a short endpoint of its crossed edge.',
                scope='Exact hypotheses on the specified point or parameter region, invoking the written sufficient theorem and its exterior-sector dependency. This does not prove the criterion always holds or verify an individual selected net.')


if __name__=='__main__':
    import argparse
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('certificate',type=Path)
    args=ap.parse_args();spec=json.loads(args.certificate.read_text());set_precision(spec.get('suggested_fractional_bits',192))
    print(json.dumps(verify(spec),indent=2))
