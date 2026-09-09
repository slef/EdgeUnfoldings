import json
from pathlib import Path
import unittest

from n6.intervals import I, set_precision
from n6.local_gate import analyze, verify, classify_routes
from n6.local_radial import verify_clearance, verify as verify_intrusion
from n6.polycert import make_certificate, verify as verify_net
from n6.regimes import curvature_sum_band


class LocalGateTests(unittest.TestCase):
    def setUp(self):
        set_precision(240)
        self.root = Path(__file__).resolve().parents[1] / 'results'

    def load(self, suffix):
        return json.loads((self.root / f'local-gate-{suffix}.certificate.json').read_text())

    def test_selected_three_chain_slit_has_all_local_pairs_safe(self):
        cert = self.load('three-chain')
        report = verify(cert)
        self.assertEqual(report['curvature_sum_band'], 'K<pi')
        self.assertTrue(report['curvature_rankings_checked'])
        self.assertEqual(report['slit_vertex'], 5)
        self.assertEqual(len(report['local_pairs_proved_safe']), 3)
        self.assertTrue(report['all_local_pairs_by_direct_cone_tests'])
        self.assertFalse(report['full_lemma_L_proved'])
        self.assertFalse(report['full_net_claimed'])
        self.assertEqual(verify_net(cert)['result'], 'verified')

    def test_two_away_corners_have_a_larger_proved_range(self):
        cert = self.load('away')
        report = verify(cert)
        self.assertEqual(report['curvature_sum_band'], 'pi<K<2pi')
        self.assertEqual((report['first_flank_direction'], report['last_flank_direction']), ('F','B'))
        self.assertTrue(report['all_local_pairs_by_direct_cone_tests'])
        self.assertEqual(verify_net(cert)['result'], 'verified')

    def test_radial_intrusion_stays_open_to_the_gate_despite_a_safe_net(self):
        cert = self.load('radial-point')
        report = analyze(cert)
        self.assertTrue(report['through_fan_route_excluded'])
        self.assertFalse(report['across_slit_route_excluded'])
        self.assertFalse(report['across_slit_cone_test'])
        self.assertEqual(report['local_pairs_proved_safe'], ['last_petal/first_fan'])
        self.assertEqual(len(report['remaining_local_pairs']), 2)
        self.assertEqual(verify_intrusion(cert)['result'], 'verified_failure_of_local_radial_separator')
        self.assertEqual(verify_net(cert)['result'], 'verified')
        with self.assertRaisesRegex(ValueError, 'leaves local pairs open'):
            verify(cert)

    def test_radial_box_keeps_all_18_coordinates_and_a_uniform_clearance(self):
        cert = self.load('radial-family')
        self.assertEqual(cert['parameter_box'], [['-1/10000','1/10000']]*18)
        self.assertEqual(analyze(cert)['curvature_sum_band'], 'K<pi')
        self.assertEqual(verify_clearance(cert)['minimum_distance_ratio'], '6/5')
        self.assertEqual(verify_intrusion(cert)['result'], 'verified_failure_of_local_radial_separator')
        self.assertEqual(verify_net(cert)['result'], 'verified')

    def test_exact_half_and_full_turn_boundaries(self):
        quarter_total, three_quarter_total = (I(0), I(1)), (I(0), I(-1))
        half_sum = curvature_sum_band(three_quarter_total, three_quarter_total)
        self.assertEqual(half_sum, 'K=pi')
        for first, last in [('B','B'), ('F','F'), ('F','B'), ('','')]:
            self.assertTrue(classify_routes(half_sum, first, last)['all_local_pairs_by_gate'])
        full_sum = curvature_sum_band(quarter_total, three_quarter_total)
        self.assertEqual(full_sum, 'K=2pi')
        self.assertTrue(classify_routes(full_sum,'F','B')['all_local_pairs_by_gate'])
        self.assertFalse(classify_routes('K>2pi','F','B')['all_local_pairs_by_gate'])

    def test_unknown_band_does_not_exclude_a_route_with_extensions(self):
        report = classify_routes(None, 'B', 'B')
        self.assertFalse(report['through_fan_route_excluded'])
        self.assertFalse(report['across_slit_route_excluded'])
        self.assertFalse(report['all_local_pairs_by_gate'])
        with self.assertRaisesRegex(ValueError, 'Both slit corners'):
            classify_routes('K<pi','B','F')

    def test_reflection_exchanges_the_two_local_mixed_pairs(self):
        cert = self.load('radial-point')
        for point in cert['coordinate_polynomials']:
            point[0][0][0] = str(-int(point[0][0][0]))
        cert['faces'] = [list(reversed(f)) for f in cert['faces']]
        cert['local_gate']['equator'] = [2,3,1,5]
        report = analyze(cert)
        self.assertEqual(report['curvature_sum_band'], 'K<pi')
        self.assertEqual(report['local_pairs_proved_safe'], ['first_petal/last_fan'])
        cert = make_certificate(cert)
        self.assertEqual(verify_net(cert)['result'], 'verified')

    def test_cut_and_selection_claims_are_checked(self):
        cert = self.load('three-chain')
        cert['local_gate']['slit_index'] = 2
        with self.assertRaisesRegex(ValueError, 'Cuts disagree'):
            analyze(cert)
        cert['cut_edges'][-1] = [1,4]
        with self.assertRaisesRegex(ValueError, 'Curvature comparison'):
            analyze(cert)
        cert['local_gate']['check_rankings'] = False
        self.assertFalse(analyze(cert)['curvature_rankings_checked'])


if __name__ == '__main__':
    unittest.main()
