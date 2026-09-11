import unittest
from n6.intervals import set_precision
from n6.prism_switch_examples import specification
from n6.prism_switch_checks import verify_sharp_fan_fallback,verify_gate_fallback
from n6.polycert import make_certificate,verify as all_pairs


class PrismSwitchChecks(unittest.TestCase):
    def setUp(self):set_precision(240)

    def test_critical_angle_switch_is_nonvacuous_on_a_full_parameter_family(self):
        s=specification('sharp',True);r=verify_sharp_fan_fallback(s)
        self.assertEqual(r['D1_wider_comparison'],'<')
        self.assertEqual(r['C1_wider_comparison'],'>')
        self.assertTrue(r['near_star_middle_obtuse'])
        self.assertEqual(all_pairs(make_certificate(s))['result'],'verified')
        with self.assertRaises(ValueError):verify_gate_fallback(s)

    def test_obtuse_to_acute_gate_switch_has_independent_whole_net_certificate(self):
        s=specification('gate',True);r=verify_gate_fallback(s)
        self.assertTrue(r['first_middle_obtuse'] and r['fallback_middle_acute'])
        self.assertEqual(r['gate_comparisons'],{'route':'>','lower_base':'>'})
        self.assertEqual(all_pairs(make_certificate(s))['result'],'verified')
        with self.assertRaises(ValueError):verify_sharp_fan_fallback(s)


if __name__=='__main__':unittest.main()
