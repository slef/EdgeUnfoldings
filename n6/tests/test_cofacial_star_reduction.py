import json
from pathlib import Path
import unittest
from n6.cofacial_star_reduction import verify,verify_case_B,verify_case_A
from n6.cofacial_case_b_examples import specification
from n6.cofacial_case_a_examples import specification as case_A_spec
from n6.flat_octahedron import original_candidates,verify_fixed_tree
from n6.intervals import set_precision
from n6.original_edge_rule import verify as budget_verify
from n6.polycert import make_certificate,verify as all_pairs,verify_overlap
from n6.sharp_vertex_patterns import report,route_data


class CofacialStarTests(unittest.TestCase):
    def setUp(self):set_precision(240)

    def test_new_case_B_point_and_open_families_replay_all_original_pairs(self):
        for kind,sharp in [('minus',{2,3}),('prism',{2,4})]:
            for region in (False,True):
                with self.subTest(kind=kind,region=region):
                    spec=specification(kind,region);result=verify_case_B(spec)
                    self.assertTrue(result['whole_net_safe_by_written_theorem'])
                    self.assertEqual({v for v,b in result['curvature_comparisons_with_pi'].items() if b=='>'},sharp)
                    self.assertEqual(all_pairs(make_certificate(spec))['result'],'verified')

    def test_wider_case_A_families_need_more_than_the_earlier_one_sided_test(self):
        for kind in ('minus','prism'):
            for region in (False,True):
                with self.subTest(kind=kind,region=region):
                    spec=case_A_spec(kind,region);r=verify_case_A(spec)
                    self.assertEqual(r['case_A_comparison'],'<')
                    self.assertFalse(r['left_condition'] or r['right_condition'])
                    self.assertTrue(r['left_wide_condition'] or r['right_wide_condition'])
                    self.assertTrue(r['whole_net_safe_by_written_theorem'])
                    with self.assertRaises(ValueError):verify_case_B(spec)
                    self.assertEqual(all_pairs(make_certificate(spec))['result'],'verified')
                    _,trees=original_candidates(spec['faces'])
                    for tree in trees:
                        with self.assertRaises(ValueError):verify_fixed_tree({**spec,'cut_edges':tree['cuts']})
                        with self.assertRaises(ValueError):budget_verify({**spec,'cut_edges':tree['cuts']})

    def test_strict_examples_are_outside_every_old_original_star_criterion(self):
        for kind in ('minus','prism'):
            spec=specification(kind);_,trees=original_candidates(spec['faces'])
            for tree in trees:
                with self.subTest(kind=kind,tree=tree):
                    altered={**spec,'cut_edges':tree['cuts']}
                    with self.assertRaises(ValueError):verify_fixed_tree(altered)
                    with self.assertRaises(ValueError):budget_verify(altered)

    def test_two_sharp_quad_corners_include_simultaneous_equality(self):
        spec=specification('minus_boundary');r=verify_case_B(spec)
        self.assertEqual([r['curvature_comparisons_with_pi'][v] for v in (2,3)],['=','='])
        self.assertEqual(all_pairs(make_certificate(spec))['result'],'verified')

    def test_all_routes_reduce_to_two_pairs_involving_the_moved_quad(self):
        for kind,total,safe in [('minus',21,19),('prism',15,13)]:
            spec=specification(kind);_,routes=route_data(spec['faces'])
            self.assertEqual(len(routes),4)
            for t in routes:
                r=verify({**spec,'cut_edges':t['cuts']})
                self.assertEqual((r['pairs_total'],r['pairs_proved']),(total,safe))
                self.assertFalse(r['whole_net_claimed'])
                self.assertTrue(all(r['movable_quadrilateral'] in p for p in r['remaining_pairs']))

    def test_all_four_routes_can_fail_on_the_same_solid_without_refuting_reduction(self):
        root=Path(__file__).resolve().parents[1]/'results';coordinates=None
        for i in range(4):
            cert=json.loads((root/f'minus-cofacial-{i}-failure.certificate.json').read_text())
            if coordinates is None:coordinates=cert['coordinate_polynomials']
            self.assertEqual(cert['coordinate_polynomials'],coordinates)
            reduction=verify(cert)
            self.assertIn(sorted(cert['overlap_witness']['faces']),reduction['remaining_pairs'])
            self.assertEqual(verify_overlap(cert)['result'],'verified_positive_area_overlap')
            with self.assertRaises(ValueError):verify_case_B(cert)
        repair=json.loads((root/'minus-cofacial-repair.certificate.json').read_text())
        self.assertEqual(repair['coordinate_polynomials'],coordinates)
        self.assertEqual(all_pairs(repair)['result'],'verified')
        self.assertTrue(verify_fixed_tree(repair)['input_tree_nonoverlapping_by_written_theorem'])

    def test_exhaustive_sharp_position_ledger(self):
        r=report()
        expected={'minus':{1:set(),2:set(),3:set()},
                  'prism':{1:set(),2:set(),3:set()}}
        for kind in expected:
            for group in r[kind]:
                self.assertEqual({tuple(p['sharp_vertices']) for p in group['patterns'] if p['status']=='open'},
                                 expected[kind][group['sharp_count']])
                self.assertEqual(len({tuple(p['sharp_vertices']) for p in group['patterns']}),group['patterns_total'])


if __name__=='__main__':unittest.main()
