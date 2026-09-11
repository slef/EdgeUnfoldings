import json
from pathlib import Path
import unittest
from n6.case_a_one_sided import planar_tests,verify
from n6.intervals import I,set_precision
from n6.polycert import verify as all_pairs


class OneSidedCaseATests(unittest.TestCase):
    def setUp(self):set_precision(240)

    def test_real_octahedron_passes_new_separator_but_not_old_angle_bounds(self):
        path=Path(__file__).resolve().parents[1]/'results/case-A-one-sided.certificate.json'
        spec=json.loads(path.read_text());report=verify(spec)
        self.assertTrue(report['left_condition']);self.assertFalse(report['right_condition'])
        self.assertFalse(report['earlier_two_angle_condition'])
        self.assertEqual(report['left_short_comparison'],'>')
        self.assertEqual(report['right_short_comparison'],'<')
        self.assertFalse(report['whole_net_claimed'])
        self.assertEqual(all_pairs(spec)['result'],'verified')
        spec['case_A_triple_index']=(spec['selection']['slit_index']+2)%4
        with self.assertRaises(ValueError):verify(spec)

    def test_contact_equality_and_unrestricted_other_apex(self):
        # alpha+beta=90 degrees; the left ray reaches p* exactly. A middle
        # triangle of side lengths 3,3,5 lies strictly inside the ray triangle.
        # The left apex angle equals theta; the right one is 135 degrees.
        result=planar_tests((I(3),I(4)),(I(4),I(3)),(I(0),I(1)),(I(-1),I(1)),I(3),I(3),I(5))
        self.assertEqual(result['left_short_comparison'],'=')
        self.assertEqual(result['left_no_wrap_comparison'],'=')
        self.assertTrue(result['left_condition'])
        self.assertFalse(result['earlier_two_angle_condition'])
        widened=planar_tests((I(3),I(4)),(I(4),I(3)),(I(-1),I(1)),(I(-1),I(1)),I(3),I(3),I(5))
        self.assertFalse(widened['left_condition'] or widened['right_condition'])

    def test_positive_phase_scaling_does_not_change_the_length_test(self):
        original=planar_tests((I(3),I(4)),(I(4),I(3)),(I(0),I(1)),(I(-1),I(1)),I(3),I(3),I(5))
        scaled=planar_tests((I(21),I(28)),(I(44),I(33)),(I(0),I(13)),(I(-17),I(17)),I(3),I(3),I(5))
        self.assertEqual(original,scaled)


if __name__=='__main__':unittest.main()
