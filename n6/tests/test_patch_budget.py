import copy
import itertools
import json
from pathlib import Path
import unittest
from n6.patch_budget import analyze, verify, pattern, prescribed_openings, sum_le
from n6.polycert import make_certificate, verify as verify_net
from n6.intervals import I, set_precision


class PatchBudgetTests(unittest.TestCase):
    def setUp(self):
        set_precision(240)
        self.root = Path(__file__).resolve().parents[1] / 'results'

    def load(self, suffix):
        return json.loads((self.root / ('patch-budget-' + suffix + '.certificate.json')).read_text())

    def test_exact_new_regimes_and_independent_nets(self):
        for suffix, regime in [('adjacent-below-pi', 'two-adjacent'),
                               ('opposite-same', 'two-opposite-same'),
                               ('opposite-facing', 'two-opposite-facing'),
                               ('three-mixed', 'three-mixed')]:
            with self.subTest(regime=regime):
                cert = self.load(suffix)
                report = verify(cert)
                self.assertEqual(report['regime'], regime)
                self.assertTrue(report['regime_has_existence_proof'])
                self.assertTrue(report['candidates'][report['selected_candidate']]['prescribed'])
                self.assertEqual(verify_net(cert)['result'], 'verified')
                count = 4 if regime == 'two-opposite-same' else 2
                self.assertEqual(sum(r['prescribed'] for r in report['candidates']), count)

    def test_family_really_has_both_poles_below_pi(self):
        cert = self.load('adjacent-family')
        self.assertEqual(len(cert['parameter_box']), 18)
        report = verify(cert)
        self.assertEqual(report['pole_curvature_bands'], {'0': '<', '1': '<'})
        self.assertEqual(verify_net(cert)['result'], 'verified')

    def test_facing_opposite_patches_do_not_need_H(self):
        cert = self.load('opposite-facing')
        report = verify(cert)
        self.assertIsNone(report['curvature_order'])
        self.assertFalse(report['sharpest_pole_required'])
        self.assertNotIn('sharpest_pole', cert['patch_budget'])

    def test_common_direction_three_patch_case_stays_open_despite_safe_example(self):
        cert = self.load('three-same')
        report = analyze(cert)
        self.assertEqual(report['regime'], 'three-same')
        self.assertFalse(report['regime_has_existence_proof'])
        self.assertEqual(report['prescribed_slit_vertices'], [])
        self.assertTrue(any(r['certified_safe'] for r in report['candidates']))
        self.assertEqual(verify_net(cert)['result'], 'verified')
        with self.assertRaisesRegex(ValueError, 'regime remains open'):
            verify(cert)

    def test_rotations_and_reflections_check_actual_selected_trees(self):
        for suffix in ('adjacent-below-pi', 'opposite-same', 'opposite-facing', 'three-mixed'):
            cert = self.load(suffix)
            expected = sorted(analyze(cert)['prescribed_slit_vertices'])
            for shift in range(4):
                rotated = copy.deepcopy(cert)
                ring = cert['patch_budget']['equator']
                rotated['patch_budget']['equator'] = ring[shift:] + ring[:shift]
                self.assertEqual(sorted(verify(rotated)['prescribed_slit_vertices']), expected)
            reflected = copy.deepcopy(cert)
            for point in reflected['coordinate_polynomials']:
                point[0][0][0] = str(-int(point[0][0][0]))
            reflected['faces'] = [list(reversed(f)) for f in reflected['faces']]
            reflected['patch_budget']['equator'] = [2, 5, 4, 3]
            report = analyze(reflected)
            candidate = next(r for r in report['candidates'] if r['prescribed'] and r['certified_safe'])
            reflected['cut_edges'] = candidate['cut_edges']
            reflected = make_certificate(reflected)
            self.assertEqual(verify(reflected)['regime'], report['regime'])
            self.assertEqual(verify_net(reflected)['result'], 'verified')

    def test_zero_one_two_and_three_pattern_boundaries(self):
        self.assertEqual(pattern(['', '', '', '']), 'zero')
        self.assertEqual(pattern(['F', '', '', '']), 'one')
        self.assertEqual(prescribed_openings(['F', '', 'F', '']), [0, 2])
        self.assertEqual(prescribed_openings(['B', '', 'B', '']), [1, 3])
        self.assertEqual(prescribed_openings(['B', 'B', 'F', '']), [0])
        self.assertEqual(prescribed_openings(['B', 'F', 'F', '']), [3])
        for invalid in (['F', 'B', '', ''], ['F']*4, ['B', 'F', 'B', '']):
            with self.assertRaises(ValueError): pattern(invalid)

    def test_positive_angle_comparisons_include_equality_and_unresolved_signs(self):
        rays = {1: (1, 1), 2: (0, 1), 3: (-1, 1)}
        for a, b, c, d in itertools.product(rays, repeat=4):
            z = [tuple(map(I, rays[i])) for i in (a, b, c, d)]
            self.assertEqual(sum_le(z[:2], z[2:]), a+b <= c+d)
        self.assertTrue(sum_le([], [(I(1), I(1))]))
        self.assertIsNone(sum_le([(I(1), I('9/10', '11/10'))], [(I(1), I(1))]))

    def test_missing_or_false_sharpness_is_rejected_when_required(self):
        cert = self.load('adjacent-below-pi')
        cert['patch_budget'].pop('sharpest_pole')
        with self.assertRaisesRegex(ValueError, 'sharpest pole'):
            verify(cert)
        cert['patch_budget']['sharpest_pole'] = 1
        with self.assertRaisesRegex(ValueError, 'Curvature comparison'):
            verify(cert)


if __name__ == '__main__':
    unittest.main()
