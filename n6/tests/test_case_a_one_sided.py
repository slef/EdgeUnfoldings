import json
from pathlib import Path
import unittest
from n6.case_a_one_sided import planar_tests,wide_planar_tests,triangle_planar_tests,length_planar_tests,verify,verify_wide,verify_lengths,classify
from n6.intervals import I,set_precision
from n6.polycert import Geometry,verify_overlap,verify as all_pairs
from n6.flat_octahedron import curvature_bands


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

    def test_wider_angle_boundary_accepts_a_short_side_with_obtuse_apex(self):
        # alpha=beta=45 degrees, so theta=90 and its wider bound is 135.
        # The .3/.8/1 middle triangle is strictly inside the ray triangle.
        args=((I(1),I(1)),(I(1),I(1)),(I(-1),I(1)),(I(1),I(1)),I('3/10'),I('4/5'),I(1))
        r=wide_planar_tests(*args)
        self.assertFalse(r['left_condition'] or r['right_condition'])
        self.assertEqual(r['left_wide_angle_comparison'],'=')
        self.assertEqual(r['left_short_comparison'],'>')
        self.assertEqual(r['right_short_comparison'],'<')
        self.assertTrue(r['left_wide_condition'])
        scaled=wide_planar_tests((I(7),I(7)),(I(11),I(11)),(I(-13),I(13)),(I(17),I(17)),*args[-3:])
        self.assertEqual(r,scaled)
        too_wide=wide_planar_tests(*args[:2],(I(-2),I(1)),*args[3:])
        self.assertFalse(too_wide['left_wide_condition'] or too_wide['right_wide_condition'])

    def test_actual_lengths_separate_the_exact_low_fan_failure_of_the_wider_test(self):
        root=Path(__file__).resolve().parents[1]/'results'
        cert=json.loads((root/'case-A-low-fan-wide-failure.certificate.json').read_text())
        with self.assertRaises(ValueError):verify_wide(cert)
        r=verify_lengths(cert);bands=curvature_bands(Geometry(cert))
        self.assertEqual(bands[r['fan']],'<')
        self.assertEqual(bands[r['equator'][r['slit_index']]],'>')
        self.assertEqual((r['left_length_margin'],r['right_length_margin']),('>','<'))
        self.assertTrue(r['left_length_condition'])
        self.assertTrue(r['left_triangle_condition'])
        self.assertEqual(all_pairs(cert)['result'],'verified')

    def test_support_triangle_bound_includes_its_exact_angle_boundary(self):
        # The middle point (.1,.1) is strictly inside the 3-4-5 ray triangle.
        # theta=90, alpha=atan(4/3); lambda=pi-atan(1/3) is the new boundary.
        args=((I(3),I(4)),(I(4),I(3)),(I(-3),I(1)),(I(1),I(1)),
              I(2).sqrt()/10,I(82).sqrt()/10,I(1))
        r=triangle_planar_tests(*args)
        self.assertEqual(r['left_triangle_angle_comparison'],'=')
        self.assertTrue(r['left_triangle_condition'])
        self.assertFalse(r['left_wide_condition'] or r['right_wide_condition'])
        beyond=length_planar_tests(*args[:2],(I(-4),I(1)),*args[3:])
        self.assertFalse(beyond['left_triangle_condition'] or beyond['right_triangle_condition'])
        self.assertTrue(beyond['left_length_condition'])

    def test_full_length_separator_accepts_tangency_and_rejects_cone_entry(self):
        # L=3,R=4,s=1,s'=17/4: the shortfall/overshoot ratio is exactly 8.
        # These three middle lengths give a strict interior middle triangle.
        args=((I(3),I(4)),(I(4),I(3)),(I(-8),I(1)),(I(1),I(1)),I(1),I('17/4'),I(5))
        r=length_planar_tests(*args)
        self.assertEqual(r['left_length_margin'],'=')
        self.assertTrue(r['left_length_condition'])
        self.assertFalse(r['left_triangle_condition'] or r['right_triangle_condition'])
        beyond=length_planar_tests(*args[:2],(I(-9),I(1)),*args[3:])
        self.assertFalse(beyond['left_length_condition'] or beyond['right_length_condition'])

    def test_length_separator_keeps_phase_scale_and_reflection(self):
        args=((I(1),I(1)),(I(1),I(1)),(I(-2),I(1)),(I(1),I(1)),I('3/10'),I('4/5'),I(1))
        r=length_planar_tests(*args)
        self.assertFalse(r['left_wide_condition'] or r['right_wide_condition'])
        self.assertTrue(r['left_length_condition'])
        scaled=length_planar_tests((I(7),I(7)),(I(11),I(11)),(I(-26),I(13)),(I(17),I(17)),*args[-3:])
        self.assertEqual(r,scaled)
        reflected=length_planar_tests(args[1],args[0],args[3],args[2],args[5],args[4],args[6])
        self.assertTrue(reflected['right_length_condition'])
        self.assertEqual(reflected['left_length_margin'],r['right_length_margin'])
        self.assertEqual(reflected['right_length_margin'],r['left_length_margin'])

    def test_exact_high_fan_overlap_has_the_remaining_obtuse_short_side_pattern(self):
        root=Path(__file__).resolve().parents[1]/'results'
        cert=json.loads((root/'case-A-high-fan-failure.certificate.json').read_text())
        r=classify(cert,wide=True)
        self.assertEqual(r['case_A_comparison'],'<')
        self.assertEqual((r['left_short_comparison'],r['right_short_comparison']),('>','<'))
        self.assertEqual(r['left_wide_angle_comparison'],'<')
        self.assertEqual(curvature_bands(Geometry(cert))[r['fan']],'>')
        self.assertEqual(verify_overlap(cert)['result'],'verified_positive_area_overlap')
        with self.assertRaises(ValueError):verify_wide(cert)
        with self.assertRaises(ValueError):verify_lengths(cert)
        repair=json.loads((root/'case-A-high-fan-repair.certificate.json').read_text())
        self.assertEqual(cert['coordinate_polynomials'],repair['coordinate_polynomials'])
        self.assertEqual(all_pairs(repair)['result'],'verified')


if __name__=='__main__':unittest.main()
