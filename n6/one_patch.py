"""Exact hypotheses and two-pole candidates for OCTA_ONE_PATCH.md."""
import json
from pathlib import Path
from n6.polycert import Geometry
from n6.half_fan import setup, opening, two_angle_indices
from n6.curvature import face_angle, verify_order, cmul, conjugate, interval_angle_le
from n6.certify import require, edge
from n6.intervals import sub, dot, det


def triangle_angle(a, b):
    """Positive-scale (cos,sin) for two noncollinear developed vectors."""
    area = det(a, b)
    require(area.lo > 0 or area.hi < 0, 'Outer-triangle angle unresolved')
    return dot(a, b), area if area.lo > 0 else -area


def cone_test(cone, two_face_angles):
    """cone + sum(two positive face angles) <= 2*pi, without wrapping.

    Their sum is strictly between 0 and 2*pi. Its complementary angle is
    therefore in that same range, where interval_angle_le is unambiguous.
    """
    return interval_angle_le(cone, conjugate(cmul(*two_face_angles)))


def hypotheses(spec):
    g = Geometry(spec)
    claim = spec['one_patch']
    v, w, ring = claim['source'], claim['opposite'], claim['equator']
    patches, directions, lookup = setup(g, v, w, ring)
    bad = [i for i, d in enumerate(directions) if d]
    require(len(bad) == 1, 'The theorem requires exactly one nonconvex patch')
    i, = bad
    sharp = claim['sharpest_pole']
    require(sharp in (v, w), 'The globally sharpest vertex must be one of the poles')
    order = verify_order(g, [(sharp, x) for x in range(6) if x != sharp])
    k = opening(directions)
    indices = two_angle_indices(directions)
    a, b = ring[i], ring[(i+1) % 4]
    convex_corner = a if directions[i] == 'F' else b
    reflex_corner = b if directions[i] == 'F' else a
    wi, vi = [lookup[frozenset((pole, a, b))] for pole in (w, v)]
    W, V = g.develop([wi]), g.develop([wi, vi])
    points = {w: W[w], v: V[v], convex_corner: V[convex_corner]}
    candidates = []
    for source, fan in ((v, w), (w, v)):
        origin = points[fan]
        cone = triangle_angle(sub(points[convex_corner], origin), sub(points[source], origin))
        angles = []
        for j in indices:
            f = lookup[frozenset((fan, ring[j], ring[(j+1) % 4]))]
            angles.append(face_angle(g.p, g.faces[f], g.h[f], fan))
        candidates.append(dict(source=source, fan_vertex=fan, slit_vertex=ring[k],
                               cut_edges=[[source, u] for u in ring] + [[fan, ring[k]]],
                               angular_test=cone_test(cone, angles),
                               cone_product=[x.pair() for x in cone],
                               two_angle_products=[[x.pair() for x in z] for z in angles]))
    return dict(result='verified_one_patch_two_pole_hypotheses', patches=patches,
                directions=directions, sharpest_pole=sharp, curvature_order=order,
                reflex_corner=reflex_corner, convex_corner=convex_corner,
                candidates=candidates,
                conclusion='At least one of the two prescribed original-edge nets is nonoverlapping by OCTA_ONE_PATCH.md.',
                scope='Exact one-patch and curvature hypotheses on this point or region. The theorem allows the four-cut source to change. It does not prove the fixed sharpest-source rule. A null angular test is unresolved, not false.')


def verify(spec):
    report = hypotheses(spec)
    cuts = {edge(*e) for e in spec['cut_edges']}
    matches = [j for j, row in enumerate(report['candidates']) if
               cuts == {edge(*e) for e in row['cut_edges']} and row['angular_test'] is True]
    require(bool(matches), 'The selected cut tree has no certified cone test')
    report['selected_candidate'] = matches[0]
    report['result'] = 'verified_one_patch_selected_net'
    return report


if __name__ == '__main__':
    import argparse
    from n6.intervals import set_precision
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path)
    ap.add_argument('--hypotheses-only', action='store_true')
    args = ap.parse_args()
    spec = json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits', 240))
    print(json.dumps((hypotheses if args.hypotheses_only else verify)(spec), indent=2))
