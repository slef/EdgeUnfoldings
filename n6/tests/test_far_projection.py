import json
import unittest
from fractions import Fraction
from pathlib import Path

from n6.far_projection import analyze, verify, at_least_quarter_turn
from n6.far_projection_examples import specification
from n6.intervals import I, set_precision
from n6.polycert import make_certificate, verify as verify_all_pairs


class FarProjectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        set_precision(240)

    def test_high_curvature_three_patch_point_uses_universal_theorem(self):
        r = verify(specification('high-curvature'))
        self.assertEqual(r['source_curvature_comparison_with_pi'], '>')
        self.assertTrue(all(c['method']=='source_curvature_at_least_pi' for c in r['target_checks']))
        self.assertTrue(r['whole_selected_net_nonoverlapping'])
        self.assertFalse(r['universal_lemma_F_proved'])
        self.assertFalse(r['whole_octahedron_case_proved'])

    def test_low_curvature_box_needs_active_pole_angle_argument(self):
        spec = specification('low-curvature-family')
        r = verify(spec)
        self.assertEqual(r['parameter_dimension'], 18)
        self.assertEqual(r['source_curvature_comparison_with_pi'], '<')
        c = r['target_checks'][1]
        self.assertEqual(c['inward_corner_comparison'], '>')
        self.assertEqual(c['method'], 'original_pole_angle_nonobtuse')
        independent = verify_all_pairs(make_certificate(spec))
        self.assertEqual(sum(independent['pairs'].values()), 28)

    def test_obtuse_angles_are_real_but_quarter_turn_repairs_them(self):
        spec = specification('obtuse-repaired')
        r = verify(spec)
        c = r['target_checks'][1]
        self.assertEqual(r['source_curvature_comparison_with_pi'], '<')
        self.assertEqual(c['inward_corner_comparison'], '>')
        self.assertLess(Fraction(c['original_pole_dot'][1]), 0)
        self.assertLess(Fraction(c['neighboring_flat_dot'][1]), 0)
        self.assertEqual(c['method'], 'short_radius_and_quarter_turn_gap')
        self.assertTrue(c['gap_at_least_pi_over_two'])
        self.assertEqual(sum(verify_all_pairs(make_certificate(spec))['pairs'].values()), 28)

    def test_quarter_turn_boundary_and_wrapping(self):
        self.assertTrue(at_least_quarter_turn((I(0), I(1))))
        self.assertTrue(at_least_quarter_turn((I(1), I(-1))))
        self.assertTrue(at_least_quarter_turn((I(-1), I(0))))
        self.assertFalse(at_least_quarter_turn((I(1), I(1))))
        self.assertIsNone(at_least_quarter_turn((I(-1,1), I(1))))

    def test_selection_cannot_change_without_the_cut_tree(self):
        spec = specification('low-curvature')
        spec['selection']['slit_index'] = 1
        with self.assertRaisesRegex(ValueError, 'Cuts disagree'):
            verify(spec)

    def test_swapped_source_cannot_inherit_sharpest_hypothesis(self):
        spec = specification('low-curvature')
        s = spec['selection']
        s['apex'], s['antipode'] = s['antipode'], s['apex']
        s['equator'] = [s['equator'][0]]+list(reversed(s['equator'][1:]))
        spec['cut_edges'] = [[s['apex'],a] for a in s['equator']]+[[s['antipode'],s['equator'][0]]]
        with self.assertRaisesRegex(ValueError, 'Curvature comparison'):
            verify(spec)

    def test_actual_cut_crossing_is_rejected_without_H(self):
        root = Path(__file__).resolve().parents[1]
        spec = json.loads((root/'results/hinge-boundary-counterexample.certificate.json').read_text())
        spec['selection'] = dict(apex=0, antipode=1, equator=[2,3,4,5], slit_index=0)
        with self.assertRaisesRegex(ValueError, 'Curvature comparison'):
            analyze(spec)


if __name__ == '__main__':
    unittest.main()
