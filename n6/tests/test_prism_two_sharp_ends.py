import json
from pathlib import Path
import unittest
from n6.families import PRISM_CUTS
from n6.flat_octahedron import original_candidates, verify_fixed_tree, curvature_bands
from n6.intervals import set_precision
from n6.original_edge_rule import verify as budget_verify
from n6.polycert import Geometry, make_certificate, verify_overlap, verify as all_pairs
from n6.prism_two_sharp_ends import specification, verify
from n6.trees import tree_data


class PrismTwoSharpEndsTests(unittest.TestCase):
    def setUp(self):set_precision(240)

    def test_strict_family_and_exact_boundaries_replay_independently(self):
        expected={'point':('>','>'),'family':('>','>'),
                  'one_boundary':('=','>'),'both_boundaries':('=','=')}
        for kind,bands in expected.items():
            with self.subTest(kind=kind):
                spec=specification(kind);report=verify(spec)
                actual=report['curvature_comparisons_with_pi']
                self.assertEqual((actual[2],actual[5]),bands)
                independent=all_pairs(make_certificate(spec))
                self.assertEqual(independent['pairs'],{'vertex_fan':13,'separating_edge':2})
                self.assertFalse(report['full_prism_type_proved'])

    def test_strict_example_is_outside_previous_original_star_criteria(self):
        spec=specification();_,trees=original_candidates(spec['faces'])
        for t in trees:
            altered={**spec,'cut_edges':t['cuts']}
            with self.assertRaises(ValueError):verify_fixed_tree(altered)
            with self.assertRaises(ValueError):budget_verify(altered)

    def test_rejects_unrestricted_failure_and_wrong_cut_tree(self):
        root=Path(__file__).resolve().parents[1]/'results'
        failure=json.loads((root/'prism-two-pair-failure.certificate.json').read_text())
        with self.assertRaises(ValueError):verify(failure)
        spec=specification();_,trees=original_candidates(spec['faces'])
        spec['cut_edges']=trees[0]['cuts']
        with self.assertRaises(ValueError):verify(spec)

    def test_one_sharp_end_does_not_suffice(self):
        root=Path(__file__).resolve().parents[1]/'results'
        cert=json.loads((root/'prism-one-sharp-failure.certificate.json').read_text())
        bands=curvature_bands(Geometry(cert))
        self.assertEqual((bands[2],bands[5]),('<','>'))
        self.assertEqual(verify_overlap(cert)['result'],'verified_positive_area_overlap')
        with self.assertRaises(ValueError):verify(cert)
        repair=json.loads((root/'prism-one-sharp-repair.certificate.json').read_text())
        self.assertEqual(cert['coordinate_polynomials'],repair['coordinate_polynomials'])
        self.assertEqual(all_pairs(repair)['result'],'verified')
        self.assertTrue(verify_fixed_tree(repair)['input_tree_nonoverlapping_by_written_theorem'])

    def test_combinatorial_reduction_retains_exactly_the_two_proved_pairs(self):
        spec=specification();data=tree_data([tuple(f) for f in spec['faces']],PRISM_CUTS)
        self.assertEqual(data['pairs'],[(0,5),(1,3)])
        self.assertEqual({frozenset(p) for p in data['hinges']},
                         {frozenset(p) for p in ((2,0),(2,1),(2,4),(4,3),(4,5))})


if __name__=='__main__':unittest.main()
