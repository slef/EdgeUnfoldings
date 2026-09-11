import json
from pathlib import Path
import unittest

from n6.intervals import set_precision
from n6.local_lemma import verify
from n6.local_lemma_examples import obtuse_example
from n6.polycert import verify as verify_net


class LocalLemmaTests(unittest.TestCase):
    def setUp(self):
        set_precision(240)

    def load(self, name):
        return json.loads((Path(__file__).resolve().parents[1] /
                           f'results/local-gate-{name}.certificate.json').read_text())

    def test_both_sides_of_the_curvature_partition_are_now_covered(self):
        for name in ('away', 'three-chain', 'radial-point', 'radial-family'):
            with self.subTest(name=name):
                spec = self.load(name)
                result = verify(spec)
                self.assertTrue(result['all_three_local_pairs_proved'])
                self.assertTrue(result['independent_through_fan_cone_check'])
                self.assertFalse(result['full_net_claimed'])
                self.assertEqual(verify_net(spec)['result'], 'verified')

    def test_disabling_the_old_gate_rankings_does_not_disable_the_theorem_hypotheses(self):
        spec = self.load('away')
        spec['local_gate'].update(source=1, fan_vertex=0, equator=[2,5,4,3],
                                  slit_index=1, check_rankings=False)
        spec['cut_edges'] = [[1,x] for x in (2,3,4,5)]+[[0,5]]
        with self.assertRaisesRegex(ValueError, 'Curvature comparison'):
            verify(spec)

    def test_slit_ranking_is_still_required_after_switching_the_opening(self):
        spec = self.load('three-chain')
        spec['local_gate'].update(slit_index=2, check_rankings=False)
        spec['cut_edges'][-1] = [1,4]
        with self.assertRaisesRegex(ValueError, 'Curvature comparison'):
            verify(spec)

    def test_reflection_preserves_the_full_lemma(self):
        spec = self.load('radial-point')
        for point in spec['coordinate_polynomials']:
            point[0][0][0] = str(-int(point[0][0][0]))
        spec['faces'] = [list(reversed(f)) for f in spec['faces']]
        spec['local_gate']['equator'] = [2,3,1,5]
        self.assertTrue(verify(spec)['all_three_local_pairs_proved'])

    def test_weaker_pole_hypothesis_includes_an_obtuse_source_angle(self):
        spec = obtuse_example()
        result = verify(spec)
        self.assertEqual(result['original_pole_triangle_angle_at_source'], 'obtuse')
        self.assertTrue(result['independent_through_fan_cone_check'])
        self.assertEqual(verify_net(spec)['result'], 'verified')
        # Do not silently advertise this weaker-hypothesis example as H.
        spec['local_gate']['check_rankings'] = True
        with self.assertRaisesRegex(ValueError, 'Curvature comparison'):
            verify(spec)


if __name__ == '__main__':
    unittest.main()
