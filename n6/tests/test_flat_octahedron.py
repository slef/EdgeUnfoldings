import unittest
from n6.intervals import set_precision
from n6.flat_octahedron import (verify_low_existence,verify_fixed_tree,
                               exact_polygon_angle_sum_pi,original_candidates)
from n6.flat_octahedron_examples import specification
from n6.low_curvature_types import verify as old_strict_verify
from n6.polycert import Geometry,make_certificate,verify as all_pairs
from n6.selected_octahedron_examples import specification as octa_spec


class FlatOctahedronTests(unittest.TestCase):
    def setUp(self):set_precision(240)

    def test_exact_pi_boundary_in_both_original_types(self):
        for name,vertex in [('minus-boundary',2),('prism-boundary',0)]:
            with self.subTest(name=name):
                spec=specification(name);g=Geometry(spec)
                self.assertEqual(exact_polygon_angle_sum_pi(g,vertex),1)
                report=verify_low_existence(spec)
                self.assertEqual(report['curvature_comparisons_with_pi'][vertex],'=')
                self.assertTrue(report['maximum_curvature_equal_to_pi_included'])
                self.assertFalse(report['input_tree_nonoverlap_checked'])
                self.assertTrue(verify_fixed_tree(spec)['input_tree_nonoverlapping_by_written_theorem'])
                self.assertEqual(all_pairs(make_certificate(spec))['result'],'verified')
                with self.assertRaisesRegex(ValueError,'strictly below pi'):old_strict_verify(spec)

    def test_high_curvature_fixed_trees_and_parameter_regions(self):
        for name in ('minus-high','prism-high'):
            for region in (False,True):
                with self.subTest(name=name,region=region):
                    spec=specification(name,region);report=verify_fixed_tree(spec)
                    self.assertTrue(report['source_curvature_at_least_pi'])
                    self.assertFalse(report['all_curvatures_at_most_pi'])
                    self.assertTrue(report['artificial_diagonals_uncut'])
                    self.assertEqual(all_pairs(make_certificate(spec))['result'],'verified')
                    with self.assertRaisesRegex(ValueError,'original curvatures'):verify_low_existence(spec)

    def test_true_original_degree_four_candidates(self):
        from n6.families import MINUS_FACES,PRISM_FACES
        for faces,count in [(MINUS_FACES,14),(PRISM_FACES,6)]:
            family,trees=original_candidates(faces)
            self.assertEqual(len(trees),count)
            original=set(map(tuple,family['original_edges']))
            for t in trees:self.assertLessEqual(set(t['cuts']),original)

    def test_wrong_type_and_uncertain_angles_not_accepted(self):
        with self.assertRaises(ValueError):verify_low_existence(octa_spec('regular-ties'))
        spec=specification('minus-high',True)
        self.assertIsNone(exact_polygon_angle_sum_pi(Geometry(spec),0))


if __name__=='__main__':unittest.main()
