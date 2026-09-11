"""Choose one prism cut tree by proved angle tests, then check its whole net.

The rule is derived in TIDY_PROOF.md, not inferred from these examples.
The independent all-pairs replay verifies only the explicit input domain.
Unresolved uniform comparisons are inconclusive, never a counterexample.
"""
from n6.certify import require
from n6.curvature import cmul, conjugate
from n6.polycert import Geometry, make_certificate, verify as all_pairs
from n6.prism_cap_rule import choose_candidates
from n6.prism_paths import polygon_angle_product
from n6.prism_switch_checks import angle, wide_comparison
from n6.regimes import two_curvatures_angle


def choose(g):
    cap = choose_candidates(g)
    options = cap['candidates']
    if len(options) == 1:
        return dict(cap_selection=cap, candidate=options[0],
                    reason='both_caps_at_least_pi', angle_checks={})
    near, fallback = options
    reflected = cap['large_cap_above_three_pi_by_total_curvature'] == 'F'
    vertices = (4, 3, 5, 1, 0, 2) if reflected else tuple(range(6))
    faces = dict(zip('ABCDEF', (5, 3, 4, 1, 2, 0) if reflected else range(6)))

    def a(face, vertex):
        return angle(g, faces[face], vertices[vertex])

    def result(candidate, reason, checks):
        return dict(cap_selection=cap, reflected_to_large_A=reflected,
                    candidate=candidate, reason=reason, angle_checks=checks)

    if cap['branch'].endswith('curvature_gate_switch'):
        first, second = a('F', 3)[0], a('F', 5)[0]
        checks = dict(F3_cosine_numerator=first.pair(),
                      F5_cosine_numerator=second.pair())
        if first.lo >= 0:
            return result(near, 'gate_middle_nonobtuse', checks)
        if first.hi < 0 or second.lo >= 0:
            return result(fallback, 'gate_fallback_middle_nonobtuse', checks)
        raise ValueError('No uniform nonobtuse gate-side choice certified')

    middle = a('E', 1)
    checks = dict(E1_cosine_numerator=middle[0].pair())
    if middle[0].lo >= 0:
        return result(near, 'sharp_middle_nonobtuse', checks)
    products = {v: polygon_angle_product(g, vertices[v]) for v in (3, 4)}
    case = two_curvatures_angle(products[3], products[4], middle)
    checks['K_compared_to_E1'] = case
    if case in ('>', '='):
        return result(near, 'sharp_residual_case_B', checks)
    require(case == '<', 'No uniform sharp-switch Case A/B branch certified')
    theta = cmul(cmul(a('E', 3), conjugate(products[3])),
                 cmul(a('E', 4), conjugate(products[4])))
    wide = wide_comparison(a('D', 1), theta)
    checks['D1_wider_bound_slack'] = wide
    if wide in ('>', '='):
        return result(near, 'sharp_wider_angle_bound', checks)
    require(wide == '<' and middle[0].hi < 0,
            'No uniform failure of both sharp near-star angle tests certified')
    return result(fallback, 'sharp_angle_identities_force_fallback', checks)


def select(spec):
    selection = choose(Geometry(spec))
    candidate = selection['candidate']
    clean = {k: v for k, v in spec.items()
             if k not in ('pair_witnesses', 'overlap_witness')}
    certificate = make_certificate({**clean, 'cut_edges': candidate['cut_edges']})
    replay = all_pairs(certificate)
    return dict(result='verified_one_tree_prism_angle_rule', selection=selection,
                certificate=certificate, independent_all_original_pairs=replay,
                number_of_trial_unfoldings_for_selection=0,
                geometric_proof_formally_verified=False,
                scope='The proved curvature and angle tests select one tree before any development. Its complete net is independently certified on this explicit domain; the universal geometry remains a separate written proof.')


def main():
    import argparse
    import json
    from pathlib import Path
    from n6.intervals import set_precision
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input', type=Path)
    ap.add_argument('--certificate', type=Path)
    args = ap.parse_args()
    set_precision(240)
    report = select(json.loads(args.input.read_text()))
    certificate = report.pop('certificate')
    if args.certificate:
        args.certificate.write_text(json.dumps(certificate, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
