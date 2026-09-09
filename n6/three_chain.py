"""Exact sufficient conditions for the common-direction three-patch theorem.

OCTA_THREE_CHAIN.md contains the geometric proof. A success here covers an
explicit subfamily; the full three-common-direction regime remains open.
"""
import json
from pathlib import Path

from n6.certify import edge, require
from n6.curvature import angle_product, cmul, conjugate, face_angle, interval_angle_le
from n6.half_fan import setup
from n6.patch_budget import analyze as analyze_patches, pattern, pole_angles_and_leans
from n6.polycert import Geometry
from n6.regimes import two_curvatures_pi


def audit_curvature_pair_failure(spec):
    """Certify that none of the three sharper-pole curvature tests applies."""
    from itertools import combinations
    from n6.curvature_pair import weighted_curvature_bound
    g = Geometry(spec)
    edges = {frozenset(e) for f in g.faces for e in combinations(f, 2)}
    pairs = [(a, b) for a, b in combinations(range(6), 2) if frozenset((a, b)) not in edges]
    require(len(pairs) == 3, 'Expected three opposite pairs')
    totals = {p: angle_product(g.p, g.faces, g.h, p) for p in range(6)}
    rows = []
    for a, b in pairs:
        order = interval_angle_le(totals[a], totals[b])
        require(order is not None, 'Opposite-pole curvature order unresolved')
        sharper, other = (a, b) if order else (b, a)
        test = weighted_curvature_bound(totals[sharper], totals[other])
        require(test is False, 'An earlier curvature-pair criterion may apply')
        rows.append(dict(sharper_pole=sharper, other_pole=other,
                         weighted_curvature_bound=False))
    return dict(result='verified_all_three_curvature_pair_tests_fail', pairs=rows,
                scope='Only the earlier sharper-pole weighted curvature criterion is excluded; other unfolding theorems may apply.')


def chain_indices(directions):
    require(pattern(directions) == 'three-same', 'Expected three bad patches with a common direction')
    start = next(i for i in range(4) if directions[i] and not directions[i-1])
    middle = (start+1) % 4
    if directions[middle] == 'F':
        first_reflex = (start+1) % 4
        middle_reflex = (start+2) % 4
        slits = [(start+2) % 4, (start+3) % 4]
    else:
        first_reflex = (start+2) % 4
        middle_reflex = (start+1) % 4
        slits = [start, (start+1) % 4]
    return dict(middle_patch=middle, first_reflex_index=first_reflex,
                middle_reflex_index=middle_reflex, slit_indices=slits)


def excess_le_curvature_sum(excess, a, b):
    """excess in (0,pi), while the positive curvature sum can exceed 2*pi."""
    band = two_curvatures_pi(a, b)
    if band in ('>', '='):
        return True
    if band == '<':
        return interval_angle_le(excess, cmul(conjugate(a), conjugate(b)))
    return None


def analyze(spec):
    budget = analyze_patches(spec)  # Certifies the globally sharpest pole as well.
    require(budget['regime'] == 'three-same', 'Expected the common-direction three-patch regime')
    g = Geometry(spec)
    claim = spec['patch_budget']
    v, w, ring = claim['source'], claim['opposite'], claim['equator']
    patches, directions, lookup = setup(g, v, w, ring)
    indices = chain_indices(directions)
    middle = indices['middle_patch']
    first_reflex = ring[indices['first_reflex_index']]
    middle_reflex = ring[indices['middle_reflex_index']]
    _, leans = pole_angles_and_leans(g, v, w, ring, directions, lookup)
    totals = {p: angle_product(g.p, g.faces, g.h, p)
              for p in {v, w, first_reflex, middle_reflex}}
    a, b = ring[middle], ring[(middle+1) % 4]
    face_angles = [face_angle(g.p, g.faces[lookup[frozenset((p, a, b))]],
                             g.h[lookup[frozenset((p, a, b))]], middle_reflex)
                   for p in (v, w)]
    reflex_product = cmul(*face_angles)
    excess = (-reflex_product[0], -reflex_product[1])  # subtract pi
    simple, middle_tests, chain_tests, curvature_tests = {}, {}, {}, {}
    for p in (v, w):
        gap = conjugate(totals[p])
        simple[str(p)] = interval_angle_le(excess, gap)
        middle_tests[str(p)] = interval_angle_le(leans[p][middle], gap)
        chain_tests[str(p)] = excess_le_curvature_sum(excess, totals[p], totals[first_reflex])
        curvature_tests[str(p)] = two_curvatures_pi(totals[p], totals[middle_reflex])
    certified = lambda values: all(x is True for x in values.values())
    simple_pass = certified(simple)
    strong_pass = certified(middle_tests) and certified(chain_tests)
    curvature_pass = all(x in ('>', '=') for x in curvature_tests.values())
    slits = [ring[i] for i in indices['slit_indices']]
    candidates = [dict(row, prescribed=row['slit_vertex'] in slits) for row in budget['candidates']]
    covered = simple_pass or strong_pass or curvature_pass
    return dict(result='verified_three_chain_analysis', directions=directions, patches=patches,
                sharpest_pole=budget['sharpest_pole'], curvature_order=budget['curvature_order'],
                middle_patch=middle, first_reflex_vertex=first_reflex,
                middle_reflex_vertex=middle_reflex, prescribed_slit_vertices=slits,
                middle_excess_product=[x.pair() for x in excess],
                simple_excess_tests=simple, middle_gap_tests=middle_tests,
                chain_excess_tests=chain_tests, curvature_sum_relations=curvature_tests,
                simple_criterion_certified=simple_pass, switch_criterion_certified=strong_pass,
                curvature_corollary_certified=curvature_pass,
                subfamily_hypotheses_certified=covered, full_regime_proved=False,
                candidates=candidates,
                conclusion=('One of the four prescribed nets is nonoverlapping by OCTA_THREE_CHAIN.md.'
                            if covered else 'These sufficient subfamily hypotheses are not certified.'),
                scope='Exact hypotheses on this point or region. The full common-direction three-patch regime and fixed sharpest-source rule remain open. Failed or unresolved sufficient tests do not imply overlap.')


def verify(spec):
    report = analyze(spec)
    require(report['subfamily_hypotheses_certified'], 'Three-chain sufficient hypotheses not certified')
    criterion = spec['three_chain']['criterion']
    require(criterion in ('simple', 'switch', 'curvature'), 'Unknown three-chain criterion')
    key = {'simple': 'simple_criterion_certified', 'switch': 'switch_criterion_certified',
           'curvature': 'curvature_corollary_certified'}[criterion]
    require(report[key], 'Requested three-chain criterion not certified')
    cuts = {edge(*e) for e in spec['cut_edges']}
    choices = [i for i, row in enumerate(report['candidates'])
               if row['prescribed'] and row['certified_safe']
               and cuts == {edge(*e) for e in row['cut_edges']}]
    require(bool(choices), 'Selected tree is not a certified prescribed three-chain net')
    report.update(result='verified_three_chain_selected_net', criterion=criterion,
                  selected_candidate=choices[0])
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
