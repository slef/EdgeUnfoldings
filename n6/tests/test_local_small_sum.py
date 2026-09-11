import json
from pathlib import Path
import unittest

from n6.intervals import set_precision
from n6.local_small_sum import verify, verify_cut_separator
from n6.polycert import make_certificate, verify as verify_net


class LocalSmallSumTests(unittest.TestCase):
    def setUp(self):
        set_precision(240)

    def load(self, name):
        return json.loads((Path(__file__).resolve().parents[1] /
                           f'results/local-gate-{name}.certificate.json').read_text())

    def test_former_radial_obstruction_is_now_inside_the_universal_branch(self):
        spec = self.load('radial-point')
        result = verify_cut_separator(spec)
        self.assertFalse(result['theorem']['angular_gate_alone_suffices'])
        self.assertTrue(result['theorem']['all_three_local_pairs_proved'])
        self.assertFalse(result['theorem']['full_lemma_L_proved'])
        self.assertFalse(result['theorem']['full_net_claimed'])
        self.assertEqual(len(result['opposite_face_checks']), 2)
        self.assertEqual(verify_net(spec)['result'], 'verified')

    def test_the_same_separator_works_on_the_entire_radial_box(self):
        result = verify_cut_separator(self.load('radial-family'))
        self.assertEqual(result['inward_petal'], 'first')
        self.assertEqual(result['theorem']['curvature_sum_band'], 'K<pi')

    def test_reflection_gives_the_other_inward_petal(self):
        spec = self.load('radial-point')
        for point in spec['coordinate_polynomials']:
            point[0][0][0] = str(-int(point[0][0][0]))
        spec['faces'] = [list(reversed(f)) for f in spec['faces']]
        spec['local_gate']['equator'] = [2,3,1,5]
        result = verify_cut_separator(spec)
        self.assertEqual(result['inward_petal'], 'last')
        self.assertEqual(verify_net(make_certificate(spec))['result'], 'verified')

    def test_it_also_accepts_the_angularly_separated_case(self):
        spec = self.load('three-chain')
        self.assertTrue(verify(spec)['angular_gate_alone_suffices'])
        with self.assertRaisesRegex(ValueError, 'No inward corner'):
            verify_cut_separator(spec)

    def test_large_sum_is_rejected_even_when_that_individual_net_is_safe(self):
        spec = self.load('away')
        self.assertEqual(verify_net(spec)['result'], 'verified')
        with self.assertRaisesRegex(ValueError, 'does not settle this curvature branch'):
            verify(spec)

    def test_slit_ranking_cannot_be_disabled_with_the_gate_flag(self):
        spec = self.load('three-chain')
        spec['local_gate'].update(check_rankings=False, slit_index=2)
        spec['cut_edges'][-1] = [1,4]
        with self.assertRaisesRegex(ValueError, 'Curvature comparison'):
            verify(spec)


if __name__ == '__main__':
    unittest.main()
