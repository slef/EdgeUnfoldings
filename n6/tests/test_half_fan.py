import copy
import json
from pathlib import Path
import unittest
from n6.half_fan import hypotheses, verify, opening, audit_two_angle_failure
from n6.polycert import make_certificate, verify as verify_net
from n6.intervals import set_precision


class HalfFanTests(unittest.TestCase):
    def setUp(self):
        set_precision(240)
        self.root = Path(__file__).resolve().parents[1] / 'results'

    def load(self, name):
        return json.loads((self.root / (name + '.certificate.json')).read_text())

    def test_four_direction_cases_have_independent_full_net_certificates(self):
        for case in ('one', 'ff', 'bb', 'bf'):
            with self.subTest(case=case):
                cert = self.load('half-fan-' + case)
                report = verify(cert)
                self.assertEqual(report['result'], 'verified_half_fan_hypotheses')
                self.assertEqual(report['fan_curvature_relation_to_pi'], '>')
                self.assertFalse(report['sharpest_source_required'])
                self.assertEqual(verify_net(cert)['result'], 'verified')

    def test_full_coordinate_family(self):
        cert = self.load('half-fan-adjacent-family')
        self.assertEqual(len(cert['parameter_box']), 18)
        self.assertEqual(verify(cert)['directions'], ['', '', 'B', 'F'])
        self.assertEqual(verify_net(cert)['result'], 'verified')

    def test_two_angle_condition_is_weaker_than_half_turn_curvature(self):
        cert = self.load('half-fan-two-angles')
        self.assertEqual(verify(cert)['two_angle_sum_relation_to_pi'], '<')
        self.assertEqual(verify_net(cert)['result'], 'verified')
        cert['half_fan']['criterion'] = 'curvature'
        with self.assertRaisesRegex(ValueError, 'fan curvature at least pi'):
            verify(cert)

    def test_exact_limit_of_exchanging_poles(self):
        cert = self.load('half-fan-angle-limit')
        report = audit_two_angle_failure(cert)
        self.assertEqual(report['pole_angle_sum_relations'], ['>', '>'])
        self.assertEqual(report['directions'], ['F', '', '', ''])
        self.assertEqual(verify_net(cert)['result'], 'verified')
        for v, w, ring in [(0, 1, [2, 3, 4, 5]), (1, 0, [2, 5, 4, 3])]:
            cert['half_fan'] = dict(source=v, fan_vertex=w, equator=ring,
                                    criterion='two_angles')
            with self.assertRaisesRegex(ValueError, 'two angles sum'):
                hypotheses(cert)

    def test_cyclic_relabeling_preserves_the_physical_cut(self):
        for case in ('one', 'ff', 'bb', 'bf', 'two-angles'):
            cert = self.load('half-fan-' + case)
            slit = verify(cert)['slit_vertex']
            ring = cert['half_fan']['equator']
            for j in range(4):
                rotated = copy.deepcopy(cert)
                rotated['half_fan']['equator'] = ring[j:] + ring[:j]
                self.assertEqual(verify(rotated)['slit_vertex'], slit)

    def test_reflection_checks_the_opposite_lean_direction(self):
        cert = self.load('half-fan-one')
        # Reflect the original solid and reverse each facet to retain its
        # outward orientation. The cyclic ring must reverse too.
        for p in cert['coordinate_polynomials']:
            p[0][0][0] = str(-int(p[0][0][0]))
        cert['faces'] = [list(reversed(f)) for f in cert['faces']]
        cert['half_fan']['equator'] = [2, 5, 4, 3]
        report = hypotheses(cert)
        self.assertIn('B', report['directions'])
        cert['cut_edges'] = report['selected_cut_edges']
        reflected = make_certificate(cert)
        self.assertEqual(verify(reflected)['result'], 'verified_half_fan_hypotheses')
        self.assertEqual(verify_net(reflected)['result'], 'verified')

    def test_invalid_cases_and_mismatched_cut_are_rejected(self):
        for directions in (['F', '', 'F', ''], ['B', 'B', 'B', ''],
                           ['F', 'B', '', ''], ['', '', '', '']):
            with self.assertRaises(ValueError):
                opening(directions)
        cert = self.load('half-fan-one')
        cert['cut_edges'][-1][1] = 2
        with self.assertRaisesRegex(ValueError, 'theorem-selected opening'):
            verify(cert)
        cert = self.load('half-fan-one')
        cert['half_fan']['equator'] = [2, 5, 4, 3]
        with self.assertRaisesRegex(ValueError, 'orientation'):
            verify(cert)


if __name__ == '__main__':
    unittest.main()
