from fractions import Fraction as F
from itertools import combinations
import unittest

from n6.intervals import set_precision
from n6.octa_face_caps import select, select_curvatures
from n6.selected_octahedron_examples import specification


class OctaFaceCapTests(unittest.TestCase):
    def setUp(self):
        set_precision(240)

    def test_rational_curvature_grid_including_all_order_ties_and_closed_bounds(self):
        # An exact finite check of the stated selection, not a realization
        # claim or a replacement for its universal inequality proof.
        checked = pi_entries = 0
        for cuts in combinations(range(1, 24), 5):
            endpoints = (0, *cuts, 24)
            numerators = [b-a for a, b in zip(endpoints, endpoints[1:])]
            if max(numerators) >= 12:
                continue
            curvatures = [F(n, 6) for n in numerators]
            selection = select_curvatures(curvatures)
            w, c = selection['fan'], selection['slit']
            self.assertTrue(curvatures[selection['source']] >= 1 or curvatures[w] <= 1)
            self.assertGreaterEqual(2*curvatures[c]+curvatures[w], 1)
            self.assertTrue(all(1 <= q <= 3 for q in selection['face_cap_sums']))
            checked += 1
            pi_entries += 6 in numerators
        self.assertGreater(checked, 25000)
        self.assertGreater(pi_entries, 0)

    def test_upper_cap_bound_can_force_the_second_fan_even_when_both_are_low(self):
        k = list(map(F, ('39/20', '49/1000', '2/25', '1/100', '19/10', '11/1000')))
        result = select_curvatures(k)
        self.assertEqual(result['fan'], 5)
        self.assertEqual(result['source'], 4)
        self.assertEqual(result['slit'], 0)

    def test_a_high_fan_is_allowed_because_its_selected_source_is_even_sharper(self):
        k = list(map(F, ('3/2', '1/20', '6/5', '11/10', '1/10', '1/20')))
        result = select_curvatures(k)
        self.assertEqual(result['fan'], 3)
        self.assertGreater(k[result['fan']], 1)
        self.assertGreaterEqual(k[result['source']], k[result['fan']])

    def test_new_cut_works_outside_the_old_source_condition(self):
        result = select(specification('high-curvature'))
        d = result['selection']
        bands = d['curvature_comparisons_with_pi']
        self.assertEqual(bands[d['slit']], '>')
        self.assertEqual(bands[d['source']], '<')
        self.assertFalse(d['old_high_source_or_all_low_condition_used'])
        self.assertTrue(d['canonical_larger_difference_choice'])
        self.assertEqual(sum(result['independent_all_28_pairs']['pairs'].values()), 28)

    def test_metric_ties_and_a_whole_threshold_crossing_domain_remain_covered(self):
        for name in ('regular-ties', 'curvature-equality', 'crossing-threshold'):
            with self.subTest(name=name):
                result = select(specification(name))
                self.assertEqual(sum(result['independent_all_28_pairs']['pairs'].values()), 28)
                self.assertTrue(result['selection']['canonical_larger_difference_choice'])
                if name == 'crossing-threshold':
                    self.assertEqual(result['independent_all_28_pairs']['parameter_dimension'], 18)


if __name__ == '__main__':
    unittest.main()
