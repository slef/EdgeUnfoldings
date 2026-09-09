import copy
import itertools
import json
from pathlib import Path
import unittest
from n6.one_patch import cone_test, hypotheses, verify
from n6.polycert import make_certificate, verify as verify_net
from n6.half_fan import audit_two_angle_failure
from n6.intervals import I, set_precision


class OnePatchTests(unittest.TestCase):
    def setUp(self):
        set_precision(240)
        self.root = Path(__file__).resolve().parents[1] / 'results'

    def load(self, name):
        return json.loads((self.root / (name + '.certificate.json')).read_text())

    def test_cone_comparison_handles_equality_and_wraps(self):
        rays = {1: (1, 1), 2: (0, 1), 3: (-1, 1)}
        for a, b, c in itertools.product(rays, repeat=3):
            z = [tuple(map(I, rays[j])) for j in (a, b, c)]
            self.assertEqual(cone_test(z[0], z[1:]), a+b+c <= 8)

    def test_both_tree_candidates_have_independent_net_checks(self):
        for index, letter in enumerate('AB'):
            cert = self.load('one-patch-' + letter)
            report = verify(cert)
            self.assertEqual(report['result'], 'verified_one_patch_selected_net')
            self.assertEqual(report['selected_candidate'], index)
            A, B = report['candidates']
            self.assertEqual(A['slit_vertex'], B['slit_vertex'])
            self.assertEqual(A['source'], B['fan_vertex'])
            self.assertEqual(A['fan_vertex'], B['source'])
            self.assertEqual([A['slit_vertex'], report['reflex_corner'], report['convex_corner']], [5, 4, 3])
            self.assertEqual(verify_net(cert)['result'], 'verified')

    def test_cones_cover_the_exact_failure_of_the_two_angle_shortcut(self):
        limit = self.load('half-fan-angle-limit')
        self.assertEqual(audit_two_angle_failure(limit)['pole_angle_sum_relations'], ['>', '>'])
        for index in range(2):
            cert = self.load('one-patch-angle-limit-' + str(index))
            self.assertEqual(verify(cert)['selected_candidate'], index)
            self.assertEqual(verify_net(cert)['result'], 'verified')

    def test_ring_rotation_and_reflection_select_the_correct_physical_endpoint(self):
        original = self.load('one-patch-A')
        for j in range(4):
            cert = copy.deepcopy(original)
            ring = cert['one_patch']['equator']
            cert['one_patch']['equator'] = ring[j:] + ring[:j]
            self.assertEqual([c['slit_vertex'] for c in verify(cert)['candidates']], [5, 5])
        reflected = copy.deepcopy(original)
        for p in reflected['coordinate_polynomials']:
            p[0][0][0] = str(-int(p[0][0][0]))
        reflected['faces'] = [list(reversed(f)) for f in reflected['faces']]
        reflected['one_patch']['equator'] = [2, 5, 4, 3]
        report = hypotheses(reflected)
        self.assertIn('B', report['directions'])
        self.assertEqual([c['slit_vertex'] for c in report['candidates']], [5, 5])
        self.assertEqual(verify(make_certificate(reflected))['selected_candidate'], 0)
        self.assertEqual(verify_net(make_certificate(reflected))['result'], 'verified')

    def test_false_curvature_ranking_and_wrong_cut_are_rejected(self):
        cert = self.load('one-patch-A')
        cert['one_patch']['sharpest_pole'] = 1
        with self.assertRaisesRegex(ValueError, 'Curvature comparison'):
            verify(cert)
        cert = self.load('one-patch-A')
        cert['cut_edges'][-1][1] = 2
        with self.assertRaisesRegex(ValueError, 'selected cut tree'):
            verify(cert)
        cert = self.load('half-fan-bf')
        cert['one_patch'] = dict(source=0, opposite=1, equator=[2, 3, 4, 5], sharpest_pole=0)
        with self.assertRaisesRegex(ValueError, 'exactly one nonconvex'):
            verify(cert)


if __name__ == '__main__':
    unittest.main()
