import copy
import json
import unittest
from pathlib import Path

from n6.intervals import set_precision
from n6.selected_octahedron_examples import specification
from n6.tidy_audit import (complement_classification, finite_entry_counterexample,
                          half_fan, minus_identity, shorter_prism_identities)


class TidyProofAuditTests(unittest.TestCase):
    def setUp(self):
        set_precision(240)

    def test_minus_identity_uses_all_original_face_angle_sums(self):
        report = minus_identity()
        self.assertEqual(report['independent_angle_indeterminates'], 15)
        self.assertFalse(report['positivity_or_geometry_formally_verified'])

    def test_shorter_prism_identities_are_exact_under_all_original_face_sums(self):
        report = shorter_prism_identities()
        self.assertEqual(report['identities'], 3)
        self.assertEqual(report['independent_angle_indeterminates'], 14)
        self.assertFalse(report['geometry_or_positivity_formally_verified'])

    def test_complements_exhaust_the_four_nonuniversal_vertex_types(self):
        report = complement_classification()
        self.assertEqual(report['retained_types'], 4)
        rows = report['component_types']
        self.assertEqual(len(rows), 8)
        self.assertEqual(sum(r.get('excluded_by') == 'K_3,3 subgraph' for r in rows), 3)
        self.assertEqual(sum(r.get('excluded_by') == 'two-vertex separator' for r in rows), 1)

    def test_real_finite_entry_satisfies_both_necessary_inequalities(self):
        path = Path(__file__).resolve().parents[1]/'results/hinge-boundary-counterexample.certificate.json'
        report = finite_entry_counterexample(json.loads(path.read_text()))
        self.assertTrue(report['source_curvature_below_pi'])
        self.assertTrue(report['equal_radius_budget_below_pi'])
        self.assertEqual(report['other_pairs_rechecked'], 27)

    def test_half_fan_direct_comparisons_in_both_source_regimes(self):
        for name in ('regular-ties', 'high-curvature', 'low-curvature',
                     'obtuse', 'curvature-equality'):
            with self.subTest(name=name):
                report = half_fan(specification(name))
                self.assertEqual(len(report['comparisons']), 4)
                self.assertFalse(report['whole_net_claimed'])

    def test_half_fan_checks_a_region_crossing_source_curvature_pi(self):
        report = half_fan(specification('crossing-threshold'))
        self.assertEqual(report['parameter_dimension'], 18)
        self.assertFalse(report['geometric_proof_formally_verified'])

    def test_reversing_poles_does_not_preserve_the_source_condition(self):
        spec = copy.deepcopy(specification('high-curvature'))
        selection = spec['selection']
        selection['apex'], selection['antipode'] = selection['antipode'], selection['apex']
        ring = selection['equator']
        selection['equator'] = ring[:1]+ring[:0:-1]
        with self.assertRaisesRegex(ValueError, 'Expected source curvature'):
            half_fan(spec)


if __name__ == '__main__':
    unittest.main()
