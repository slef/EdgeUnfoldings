import unittest

from n6.intervals import set_precision
from n6.sharpest_cofacial import check


class SharpestCofacialTests(unittest.TestCase):
    def setUp(self):
        set_precision(240)

    def test_integer_example_has_two_failed_sharpest_source_routes_and_three_safe_alternatives(self):
        result = check()
        self.assertEqual(result['strictly_sharpest_source'], 1)
        self.assertEqual(len(result['strict_source_comparisons']), 5)
        self.assertEqual([r['overlap_faces'] for r in result['failed_routes']], [[0, 3], [3, 4]])
        self.assertTrue(all(r['exact_replay']['result'] == 'verified_positive_area_overlap'
                            for r in result['failed_routes']))
        self.assertTrue(all(sum(r['exact_replay']['pairs'].values()) == 15
                            for r in result['successful_routes']))
        self.assertEqual(result['cap_rule_prescribed_success']['selection']['candidate']['name'],
                         'triangular_chain_fallback')

    def test_same_strict_failure_and_curvature_order_hold_in_a_full_parameter_neighborhood(self):
        result = check(family=True)
        self.assertTrue(result['positive_parameter_width'])
        self.assertEqual(result['parameter_dimension'], 9)
        self.assertEqual(result['curvature_comparisons_with_pi'][1], '>')
        self.assertEqual(sum(result['cap_rule_prescribed_success']['independent_all_original_pairs']['pairs'].values()), 15)


if __name__ == '__main__':
    unittest.main()
