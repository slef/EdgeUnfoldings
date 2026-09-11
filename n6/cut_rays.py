"""Exact one-dimensional tests for the selected-slit Lemma F reduction.

The written theorem is LEMMA_F_CUT_RAYS.md. Empty relaxed clipping intervals
prove safety; inconclusive interval arithmetic never certifies a collision.
"""
import json
from fractions import Fraction
from pathlib import Path

from n6.certify import require, tree_path
from n6.curvature import face_angle
from n6.far_pairs import labels, targets
from n6.intervals import det, sub
from n6.polycert import Geometry
from n6.regimes import classify, positive_angles_pi


def clip_entry(triangle, origin, endpoint, finite=True):
    """Exclude petal-interior entry for x(t), 0<t<1 or 0<t<infinity.

    All three triangle vertices must be supplied in counterclockwise order.
    For t>=0, c.hi+t*d.hi bounds the true oriented-edge determinant above.
    The resulting feasible interval is an outer bound, not a collision test.
    """
    require(len(triangle) == 3, 'Expected a triangle')
    require(det(sub(triangle[1], triangle[0]),
                sub(triangle[2], triangle[0])).lo > 0,
            'Petal orientation not strictly certified')
    direction = sub(endpoint, origin)
    lower, upper = Fraction(0), Fraction(1) if finite else None
    impossible = False
    edges = []
    for a, b in zip(triangle, triangle[1:]+triangle[:1]):
        c = det(sub(b, a), sub(origin, a))
        d = det(sub(b, a), direction)
        edges.append(dict(constant=c.pair(), slope=d.pair()))
        if d.hi > 0:
            lower = max(lower, -c.hi/d.hi)
        elif d.hi < 0:
            bound = -c.hi/d.hi
            upper = bound if upper is None else min(upper, bound)
        elif c.hi <= 0:
            impossible = True
    empty = impossible or upper is not None and lower >= upper
    return dict(interior_entry_excluded=empty,
                domain='open_segment' if finite else 'open_ray',
                relaxed_lower=str(lower),
                relaxed_upper=None if upper is None else str(upper),
                constant_obstruction=impossible, edge_bounds=edges)


def checks(spec, g):
    _, w, ring, k, _, _ = labels(spec, g)
    result = []
    for petal_id, fan_id in targets(spec, g):
        fan = g.develop((fan_id,))
        petal = g.develop(tree_path(g.adj, fan_id, petal_id))
        triangle = [petal[v] for v in g.faces[petal_id]]
        origin, endpoint = fan[w], fan[ring[k]]
        result.append(dict(petal=petal_id, fan=fan_id, cut_edge=[w, ring[k]],
                           finite_segment=clip_entry(triangle, origin, endpoint),
                           infinite_ray=clip_entry(triangle, origin, endpoint, False)))
    return result


def make_certificate(spec):
    clean = {k: v for k, v in spec.items() if k not in
             ('pair_witnesses', 'far_pair_witnesses', 'overlap_witness',
              'angular_claims', 'apex_entry')}
    verify(clean)
    return clean


def verify(spec):
    classification = classify(spec)
    g = Geometry(spec)
    result = checks(spec, g)
    require(all(r['finite_segment']['interior_entry_excluded'] for r in result),
            'Cut-segment entry unresolved; no whole-net certificate')
    _, _, ring, k, V, W = labels(spec, g)
    directions = []
    for i in range(4):
        corners = [positive_angles_pi([
            face_angle(g.p, g.faces[f], g.h[f], x) for f in (V[i], W[i])
        ]) for x in (ring[i], ring[(i+1)%4])]
        e, f = corners
        direction = ('backward' if e == '>' else 'forward' if f == '>' else
                     'convex' if e in ('<','=') and f in ('<','=') else 'unresolved')
        directions.append(dict(patch=i, direction=direction, corner_comparisons=corners))
    direction_rule = (directions[(k+1)%4]['direction'] in ('convex','forward') and
                      directions[(k+2)%4]['direction'] in ('convex','backward'))
    return dict(result='verified_two_cut_segment_net_certificate',
                parameter_dimension=len(g.box),
                curvature_order=classification['curvature_order'],
                explicitly_checked_cut_segments=2, cut_checks=result,
                both_infinite_rays_also_clear=all(
                    r['infinite_ray']['interior_entry_excluded'] for r in result),
                patch_directions=directions, direction_only_corollary_applies=direction_rule,
                whole_selected_net_nonoverlapping=True,
                universal_lemma_F_proved=False,
                theorem_dependencies=['LEMMA_L_PROOF.md', 'LEMMA_F_CUT_RAYS.md',
                                      'LEMMA_F_CUT_REDUCTION.md',
                                      'CASE_PARTITION.md', 'HINGE_AUDIT.md'],
                scope='Exact clipping and the geometric reduction certify this explicit region only. Universal cut-segment and ray claims remain open.')


def main():
    import argparse
    from n6.intervals import set_precision
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path)
    args = ap.parse_args()
    spec = json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits', 240))
    print(json.dumps(verify(spec), indent=2))


if __name__ == '__main__':
    main()
