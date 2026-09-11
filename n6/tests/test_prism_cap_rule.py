import json
import unittest
from pathlib import Path

from n6.families import PRISM_CUTS, PRISM_FACES
from n6.intervals import set_precision
from n6.polycert import Geometry, verify_overlap
from n6.prism_cap_rule import candidates, cap_bands, choose_candidates, identities, select


ROOT = Path(__file__).resolve().parents[1]/'results'


def load(name):
    return json.loads((ROOT/(name+'.certificate.json')).read_text())


class PrismCapRuleTests(unittest.TestCase):
    def setUp(self):
        set_precision(240)

    def test_cap_identities_hold_over_every_original_face_angle_sum(self):
        report = identities()
        self.assertEqual(report['cap_identities'], 4)
        self.assertEqual(report['independent_angle_indeterminates'], 14)
        self.assertFalse(report['geometric_proof_formally_verified'])

    def test_five_original_trees_are_closed_under_the_actual_reflection(self):
        family = candidates()
        self.assertEqual(len(family), 5)
        edges = {tuple(sorted((a, b))) for f in PRISM_FACES
                 for a, b in zip(f, f[1:]+f[:1])}
        cuts = {frozenset(tuple(sorted(e)) for e in t['cut_edges']) for t in family}
        self.assertEqual(len(cuts), 5)
        reflection = (4, 3, 5, 1, 0, 2)
        for tree in cuts:
            self.assertEqual(len(tree), 5)
            self.assertTrue(tree <= edges)
            self.assertIn(frozenset(tuple(sorted((reflection[a], reflection[b])))
                                    for a, b in tree), cuts)
        self.assertEqual({(t['source'], t['slit']) for t in family[:-1]},
                         {(1, 2), (1, 4), (3, 0), (3, 5)})

    def test_all_low_curvature_family_uses_the_fixed_fallback_alone(self):
        result = select(load('low-curvature-prism-family'))
        self.assertEqual(result['selection']['branch'], 'both_cap_sums_at_least_pi')
        self.assertEqual(result['selected_candidate'], 'triangular_chain_fallback')
        self.assertEqual(result['cut_edges'], [list(e) for e in PRISM_CUTS])
        self.assertGreater(result['independent_all_original_pairs']['parameter_dimension'], 0)
        self.assertEqual(sum(result['independent_all_original_pairs']['pairs'].values()), 15)

    def test_each_of_the_four_asymmetric_branches_selects_only_its_proved_pair(self):
        cases = {
            'prism-switch-sharp-family': ('large_cap_A_sharp_end_switch', 'source_1_slit_2'),
            'prism-complementary-family': ('large_cap_A_curvature_gate_switch', 'source_3_slit_0'),
            'prism-one-sharp-failure': ('large_cap_F_sharp_end_switch', 'source_3_slit_5'),
            'prism-two-pair-failure': ('large_cap_F_curvature_gate_switch', 'source_1_slit_4'),
        }
        for name, (branch, near) in cases.items():
            with self.subTest(name=name):
                result = select(load(name))
                self.assertEqual(result['selection']['branch'], branch)
                self.assertEqual([t['name'] for t in result['selection']['candidates']],
                                 [near, 'triangular_chain_fallback'])
                self.assertIn(result['selected_candidate'], (near, 'triangular_chain_fallback'))
                self.assertEqual(sum(result['independent_all_original_pairs']['pairs'].values()), 15)

    def test_both_preserved_fallback_counterexamples_fail_the_cap_condition(self):
        for name in ('prism-two-pair-failure', 'prism-one-sharp-failure'):
            with self.subTest(name=name):
                spec = load(name)
                self.assertEqual(verify_overlap(spec)['result'], 'verified_positive_area_overlap')
                caps, _ = cap_bands(Geometry(spec))
                self.assertIn('<', caps.values())
                result = select(spec)
                self.assertNotEqual(result['selected_candidate'], 'triangular_chain_fallback')

    def test_original_endpoint_curvature_equalities_remain_covered(self):
        for name in ('prism-two-sharp-one-boundary', 'prism-two-sharp-both-boundaries'):
            with self.subTest(name=name):
                report = choose_candidates(Geometry(load(name)))
                self.assertIn('=', report['vertex_curvature_comparisons'].values())
                self.assertEqual(report['branch'], 'both_cap_sums_at_least_pi')


if __name__ == '__main__':
    unittest.main()
