"""Exact geometry, patch-pattern, and cone checks for OCTA_PATCH_BUDGET.md.

The universal case proofs are written mathematics. This module verifies
their hypotheses on a point or region and can independently choose a net
by all six sufficient angular inequalities. It uses no floating arithmetic.
"""
import json
from pathlib import Path
from n6.certify import require, edge
from n6.polycert import Geometry
from n6.half_fan import setup, opening
from n6.one_patch import triangle_angle
from n6.curvature import face_angle, angle_product, cmul, conjugate, interval_angle_le, verify_order
from n6.regimes import curvature_pi
from n6.intervals import I, sub


def pattern(directions):
    require(len(directions) == 4 and set(directions) <= {'', 'F', 'B'}, 'Invalid directions')
    bad = [i for i, d in enumerate(directions) if d]
    require(len(bad) <= 3, 'Four nonconvex patches are impossible')
    require(all(not (directions[i] == 'F' and directions[(i+1) % 4] == 'B')
                for i in range(4)), 'Two reflex corners at the same vertex')
    if len(bad) < 2:
        return ('zero', 'one')[len(bad)]
    if len(bad) == 2:
        if (bad[1]-bad[0]) % 4 in (1, 3):
            return 'two-adjacent'
        return 'two-opposite-same' if directions[bad[0]] == directions[bad[1]] else 'two-opposite-facing'
    return 'three-same' if len({directions[i] for i in bad}) == 1 else 'three-mixed'


def sum_le(left, right):
    """Compare sums known to lie in [0,2*pi) and (0,2*pi), respectively.

    Empty left is exactly zero. All nonempty summands are positive; callers
    ensure each two-term left sum is below 2*pi and each right sum is below
    2*pi. This avoids treating an unresolved or wrapped phase as zero.
    """
    if not left:
        return True
    require(1 <= len(left) <= 2 and 1 <= len(right) <= 2, 'Invalid angle sum')
    product = lambda values: values[0] if len(values) == 1 else cmul(*values)
    return interval_angle_le(product(left), product(right))


def prescribed_openings(directions):
    """Original ring indices; retain these physical vertices on pole exchange."""
    regime = pattern(directions)
    bad = [i for i, d in enumerate(directions) if d]
    if regime == 'zero':
        return list(range(4))
    if regime in ('one', 'two-adjacent'):
        return [opening(directions)]
    if regime == 'two-opposite-same':
        return bad if directions[bad[0]] == 'F' else [(i+1) % 4 for i in bad]
    if regime == 'two-opposite-facing':
        return [next(i for i in bad if directions[i] == 'F')]
    if regime == 'three-mixed':
        i = next(j for j in bad if not directions[(j-1) % 4])
        block = ''.join(directions[(i+j) % 4] for j in range(3))
        require(block in ('BBF', 'BFF'), 'Invalid mixed three-patch block')
        return [(i + (0 if block == 'BBF' else 3)) % 4]
    return []


def wedge_tests(angles, gap, directions, leans, k):
    def L(i, d):
        i %= 4
        return [leans[i]] if directions[i] == d else []
    a = lambda i: angles[i % 4]
    rows = [
        (L(k, 'F')+L(k+2, 'B'), [a(k+1)]),
        (L(k, 'B')+L(k+2, 'F'), [a(k-1), gap]),
        (L(k+1, 'F')+L(k-1, 'B'), [a(k+2)]),
        (L(k+1, 'B')+L(k-1, 'F'), [gap, a(k)]),
        (L(k, 'B')+L(k-1, 'F'), [gap]),
        (L(k, 'F')+L(k-1, 'B'), [a(k+1), a(k+2)]),
    ]
    # Every lean is below pi. A fan face angle plus the gap is below 2*pi,
    # since the other three positive face angles complete the fan.
    return [sum_le(left, right) for left, right in rows]


def pole_angles_and_leans(g, v, w, ring, directions, lookup):
    """Original physical patch indices, with extensions viewed from either pole."""
    angles = {p: [] for p in (v, w)}
    leans = {p: [] for p in (v, w)}
    for i in range(4):
        a, b = ring[i], ring[(i+1) % 4]
        wi, vi = [lookup[frozenset((pole, a, b))] for pole in (w, v)]
        for pole, fi in ((w, wi), (v, vi)):
            angles[pole].append(face_angle(g.p, g.faces[fi], g.h[fi], pole))
        if not directions[i]:
            for pole in (v, w): leans[pole].append((I(1), I(0)))
            continue
        W, V = g.develop([wi]), g.develop([wi, vi])
        c = a if directions[i] == 'F' else b
        points = {w: W[w], v: V[v], c: V[c]}
        for pole, other in ((w, v), (v, w)):
            cone = triangle_angle(sub(points[c], points[pole]), sub(points[other], points[pole]))
            leans[pole].append(cmul(cone, conjugate(angles[pole][i])))
    return angles, leans


def analyze(spec):
    g = Geometry(spec)
    claim = spec['patch_budget']
    v, w, ring = claim['source'], claim['opposite'], claim['equator']
    patches, directions, lookup = setup(g, v, w, ring)
    regime = pattern(directions)
    sharp = claim.get('sharpest_pole')
    ranking_required = regime not in ('zero', 'two-opposite-facing')
    require(sharp in (v, w) or (sharp is None and not ranking_required), 'A globally sharpest pole is required')
    order = verify_order(g, [(sharp, x) for x in range(6) if x != sharp]) if sharp is not None else None
    prescribed = [ring[i] for i in prescribed_openings(directions)]
    # All eight candidate trees retain every equator edge. Development of a
    # patch uses that uncut edge, independently of where the fan is opened.
    expected = [{edge(source, u) for u in ring} | {edge(fan, q)}
                for source, fan in ((v, w), (w, v)) for q in ring]
    require({edge(*e) for e in spec['cut_edges']} in expected, 'Expected a two-pole star-plus-one-edge tree')
    angles, leans = pole_angles_and_leans(g, v, w, ring, directions, lookup)
    totals = {p: angle_product(g.p, g.faces, g.h, p) for p in (v, w)}
    candidates = []
    for source, fan in ((v, w), (w, v)):
        if fan == w:
            ring_p, d, a, l = ring, directions, angles[fan], leans[fan]
        else:
            ring_p = [ring[0], ring[3], ring[2], ring[1]]
            d = [{'F': 'B', 'B': 'F', '': ''}[x] for x in reversed(directions)]
            a, l = list(reversed(angles[fan])), list(reversed(leans[fan]))
        for k in range(4):
            tests = wedge_tests(a, conjugate(totals[fan]), d, l, k)
            candidates.append(dict(source=source, fan_vertex=fan, slit_vertex=ring_p[k],
                                   cut_edges=[[source, u] for u in ring_p]+[[fan, ring_p[k]]],
                                   six_angular_tests=tests, certified_safe=all(x is True for x in tests),
                                   prescribed=ring_p[k] in prescribed))
    proven = regime != 'three-same'
    return dict(result='verified_patch_budget_analysis', regime=regime, directions=directions,
                patches=patches, sharpest_pole=sharp, curvature_order=order,
                sharpest_pole_required=ranking_required, prescribed_slit_vertices=prescribed,
                pole_curvature_bands={str(p): curvature_pi(totals[p]) for p in (v, w)},
                regime_has_existence_proof=proven, candidates=candidates,
                conclusion=('Some two-pole star-plus-one-edge net is nonoverlapping by OCTA_PATCH_BUDGET.md.'
                            if proven else 'The common-direction three-patch family remains open in general.'),
                scope='Exact hypotheses on this point or region. The written existence proof may exchange the four-cut source. None or false in a sufficient angular test does not prove actual overlap.')


def verify(spec):
    report = analyze(spec)
    require(report['regime_has_existence_proof'], 'The common-direction three-patch regime remains open')
    cuts = {edge(*e) for e in spec['cut_edges']}
    selected = [i for i, row in enumerate(report['candidates']) if
                row['certified_safe'] and row['prescribed'] and cuts == {edge(*e) for e in row['cut_edges']}]
    require(bool(selected), 'Selected tree does not pass every angular test')
    report.update(result='verified_patch_budget_selected_net', selected_candidate=selected[0])
    return report


if __name__ == '__main__':
    import argparse
    from n6.intervals import set_precision
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path)
    ap.add_argument('--analyze', action='store_true')
    args = ap.parse_args()
    spec = json.loads(args.certificate.read_text())
    set_precision(spec.get('suggested_fractional_bits', 240))
    print(json.dumps((analyze if args.analyze else verify)(spec), indent=2))
