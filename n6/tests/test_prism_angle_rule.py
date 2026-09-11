import json
from pathlib import Path
import unittest
from unittest.mock import patch

from n6.intervals import set_precision
from n6.polycert import Geometry
from n6.prism_angle_rule import choose, select
from n6.prism_cap_examples import NAMES

ROOT = Path(__file__).resolve().parents[1]/'results'


def load(name):
    return json.loads((ROOT/(name+'.certificate.json')).read_text())


class PrismAngleRuleTests(unittest.TestCase):
    def setUp(self):
        set_precision(240)

    def test_one_prescribed_tree_is_independently_safe_on_all_preserved_domains(self):
        for name in NAMES:
            with self.subTest(name=name):
                report = select(load(name))
                self.assertEqual(sum(report['independent_all_original_pairs']['pairs'].values()), 15)
                self.assertEqual(report['number_of_trial_unfoldings_for_selection'], 0)
                self.assertFalse(report['geometric_proof_formally_verified'])

    def test_sharp_switch_uses_the_proved_fallback_on_a_full_parameter_domain(self):
        report = select(load('prism-switch-sharp-family'))
        decision = report['selection']
        self.assertEqual(decision['reason'], 'sharp_angle_identities_force_fallback')
        self.assertEqual(decision['candidate']['name'], 'triangular_chain_fallback')
        self.assertEqual(decision['angle_checks']['D1_wider_bound_slack'], '<')
        self.assertGreater(report['independent_all_original_pairs']['parameter_dimension'], 0)

    def test_selection_uses_original_geometry_without_developing_trial_nets(self):
        for name in ('prism-complementary-family', 'prism-complementary-reflected',
                     'prism-one-sharp-failure', 'prism-switch-sharp-family'):
            with self.subTest(name=name):
                g = Geometry(load(name))
                with patch.object(g, 'develop', side_effect=AssertionError('Unexpected trial unfolding')):
                    choice = choose(g)
                self.assertEqual(len(choice['candidate']['cut_edges']), 5)


if __name__ == '__main__':
    unittest.main()
