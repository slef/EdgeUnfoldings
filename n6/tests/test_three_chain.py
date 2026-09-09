import copy
import json
from pathlib import Path
import unittest

from n6.intervals import I, set_precision
from n6.polycert import make_certificate, verify as verify_net
from n6.three_chain import (analyze, verify, chain_indices,
                            excess_le_curvature_sum, audit_curvature_pair_failure)


class ThreeChainTests(unittest.TestCase):
    def setUp(self):
        set_precision(240)
        self.root = Path(__file__).resolve().parents[1] / 'results'

    def load(self, suffix):
        return json.loads((self.root / f'three-chain-{suffix}.certificate.json').read_text())

    def test_simple_and_strictly_stronger_examples_have_independent_nets(self):
        for suffix, simple in [('simple', True), ('switch', False)]:
            with self.subTest(suffix=suffix):
                cert = self.load(suffix)
                report = verify(cert)
                self.assertEqual(report['simple_criterion_certified'], simple)
                self.assertTrue(report['switch_criterion_certified'])
                self.assertFalse(report['full_regime_proved'])
                self.assertEqual(sum(r['prescribed'] for r in report['candidates']), 4)
                self.assertEqual(verify_net(cert)['result'], 'verified')
                audit = audit_curvature_pair_failure(cert)
                self.assertEqual(len(audit['pairs']), 3)

    def test_all_eighteen_coordinates_vary_with_a_fixed_net(self):
        cert = self.load('family')
        self.assertEqual(cert['parameter_box'], [['-1/100', '1/100']]*18)
        self.assertTrue(verify(cert)['switch_criterion_certified'])
        self.assertIn(False, analyze(cert)['simple_excess_tests'].values())
        self.assertEqual(verify_net(cert)['result'], 'verified')
        self.assertEqual(len(audit_curvature_pair_failure(cert)['pairs']), 3)

    def test_uncovered_example_really_fails_a_hypothesis_but_unfolds(self):
        cert = self.load('uncovered')
        report = analyze(cert)
        self.assertFalse(report['subfamily_hypotheses_certified'])
        self.assertIn(False, report['middle_gap_tests'].values())
        self.assertTrue(any(r['certified_safe'] for r in report['candidates']))
        self.assertEqual(verify_net(cert)['result'], 'verified')
        with self.assertRaisesRegex(ValueError, 'sufficient hypotheses not certified'):
            verify(cert)

    def test_rotating_and_reflecting_preserves_the_physical_prescription(self):
        cert = self.load('switch')
        expected = sorted(verify(cert)['prescribed_slit_vertices'])
        for shift in range(4):
            rotated = copy.deepcopy(cert)
            ring = cert['patch_budget']['equator']
            rotated['patch_budget']['equator'] = ring[shift:] + ring[:shift]
            report = verify(rotated)
            self.assertEqual(sorted(report['prescribed_slit_vertices']), expected)
            self.assertEqual(report['first_reflex_vertex'], 3)
            self.assertEqual(report['middle_reflex_vertex'], 4)
        reflected = copy.deepcopy(cert)
        for point in reflected['coordinate_polynomials']:
            point[0][0][0] = str(-int(point[0][0][0]))
        reflected['faces'] = [list(reversed(f)) for f in reflected['faces']]
        reflected['patch_budget']['equator'] = [2, 5, 4, 3]
        report = verify(reflected)
        self.assertEqual(sorted(report['prescribed_slit_vertices']), expected)
        self.assertEqual(report['first_reflex_vertex'], 3)
        self.assertEqual(report['middle_reflex_vertex'], 4)
        reflected = make_certificate(reflected)
        self.assertEqual(verify_net(reflected)['result'], 'verified')

    def test_requested_stronger_shortcut_is_not_silently_relaxed(self):
        cert = self.load('switch')
        for criterion in ('simple', 'curvature'):
            cert['three_chain']['criterion'] = criterion
            with self.assertRaisesRegex(ValueError, 'Requested three-chain criterion not certified'):
                verify(cert)

    def test_nonprescribed_tree_and_false_sharpness_are_rejected(self):
        cert = self.load('switch')
        cert['cut_edges'][-1] = [1, 2]
        with self.assertRaisesRegex(ValueError, 'prescribed three-chain net'):
            verify(cert)
        cert = self.load('switch')
        cert['patch_budget']['sharpest_pole'] = 1
        with self.assertRaisesRegex(ValueError, 'Curvature comparison'):
            verify(cert)

    def test_curvature_sum_comparison_includes_equality_and_large_sums(self):
        quarter_curvature = (I(1), I(-1))
        self.assertTrue(excess_le_curvature_sum((I(0), I(1)), quarter_curvature, quarter_curvature))
        self.assertFalse(excess_le_curvature_sum((I(-1), I(1)), quarter_curvature, quarter_curvature))
        self.assertTrue(excess_le_curvature_sum((I(-1), I(1)), (I(1), I(1)), (I(1), I(1))))
        self.assertTrue(excess_le_curvature_sum((I(-1), I(1)), (I(0), I(-1)), (I(0), I(-1))))
        self.assertIsNone(excess_le_curvature_sum((I(0), I(1)), quarter_curvature, (I(1), I(-1, 1))))

    def test_chain_indices_reject_other_patterns(self):
        for directions in (['F', 'F', '', ''], ['B', 'F', 'F', ''], ['F']*4):
            with self.assertRaises(ValueError):
                chain_indices(directions)
        self.assertEqual(chain_indices(['F', 'F', 'F', ''])['slit_indices'], [2, 3])
        self.assertEqual(chain_indices(['B', 'B', 'B', ''])['slit_indices'], [0, 1])


if __name__ == '__main__':
    unittest.main()
