"""Exact counterexample to the old conditional far-fan reduction.

The selected source is not sharpest. This refutes the reduction as stated,
not its unproved sharpest-source variant or the four-choice conjecture.
"""
import itertools,json
from pathlib import Path
from n6.polycert import Geometry,verify_overlap
from n6.certify import require,tree_path
from n6.curvature import angle_product,interval_angle_le
from n6.intervals import I,sub,det


def verify(spec):
    g=Geometry(spec);claim=spec['hinge_audit']
    v,w,u,sharper=[claim[k] for k in ('source','sector_vertex','slit_vertex','sharper_vertex')]
    adjacent={x:set().union(*(set(f)-{x} for f in g.faces if x in f)) for x in range(6)}
    require(all(len(s)==4 for s in adjacent.values()) and w not in adjacent[v] and v!=w,
            'Expected opposite octahedron vertices')
    require(u in adjacent[w],'Invalid slit')
    expected={tuple(sorted((v,x))) for x in adjacent[v]}|{tuple(sorted((w,u)))}
    require({tuple(sorted(e)) for e in spec['cut_edges']}==expected,'Unexpected cut tree')
    overlapping=tuple(spec['overlap_witness']['faces'])
    require(set(g.faces[overlapping[0]]).isdisjoint(g.faces[overlapping[1]]),'Not a far-fan pair')
    require(any(v in g.faces[f] for f in overlapping) and any(w in g.faces[f] for f in overlapping),
            'Expected one petal and one fan face')
    overlap=verify_overlap(spec)
    fan=next(f for f in overlapping if w in g.faces[f])
    petal=next(f for f in overlapping if v in g.faces[f])
    require(u in g.faces[fan],'Expected entry at a slit-side fan triangle')
    fan_xy=g.develop((fan,));petal_xy=g.develop(tree_path(g.adj,fan,petal))
    t=I(claim['cut_crossing_fraction']);require(t.lo>0 and t.hi<1,'Invalid cut crossing fraction')
    x=tuple((1-t)*a+t*b for a,b in zip(fan_xy[w],fan_xy[u]));f=g.faces[petal]
    require(all(det(sub(petal_xy[b],petal_xy[a]),sub(x,petal_xy[a])).lo>0
                for a,b in zip(f,f[1:]+f[:1])), 'Slit edge does not cross petal interior')
    remaining=set(itertools.combinations(range(8),2))-{overlapping};counts={}
    for witness in spec['nonoverlap_witnesses']:
        pair=tuple(witness['faces']);require(pair in remaining,'Repeated or invalid safe pair')
        remaining.remove(pair);a,b=pair;kind=witness['kind']
        if kind=='vertex_fan':
            path=tree_path(g.adj,a,b)
            require(all(witness['vertex'] in g.faces[f] for f in path),'Wrong shared copy')
        elif kind=='separating_edge':
            require(all(q.hi<=0 for q in g.separating_bounds(a,b,witness['owner'],witness['edge'])),
                    'Safe-pair separator not certified')
        else:raise ValueError('Unknown safe-pair proof')
        counts[kind]=counts.get(kind,0)+1
    require(not remaining,'Missing safe pairs')
    total_source=angle_product(g.p,g.faces,g.h,v)
    total_sharper=angle_product(g.p,g.faces,g.h,sharper)
    require(interval_angle_le(total_source,total_sharper) is False,
            'Must certify that the selected source is not sharpest')
    return dict(result='verified_counterexample_to_conditional_far_fan_reduction',
                source=v,opposite=w,slit_vertex=u,strictly_sharper_vertex=sharper,
                overlap=overlap,nonoverlapping_pairs=27,safe_pair_methods=counts,
                crossed_cut_edge=[w,u],crossing_fraction=claim['cut_crossing_fraction'],
                local_pairs_all_clear=True,opposite_petal_pairs_all_clear=True,
                scope='The one indicated far-fan pair overlaps; all other 27 face pairs are nonoverlapping. The source is not sharpest. This refutes the old unrestricted conditional reduction, not the H-specific conjectures or edge unfoldability.')


if __name__=='__main__':
    import argparse
    from n6.intervals import set_precision
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('certificate',type=Path)
    args=ap.parse_args();spec=json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits',240))
    print(json.dumps(verify(spec),indent=2))
