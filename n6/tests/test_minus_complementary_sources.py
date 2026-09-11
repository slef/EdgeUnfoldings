import json
from pathlib import Path
import unittest
from n6.intervals import set_precision
from n6.minus_complementary_sources import select
from n6.minus_complementary_examples import specification
from n6.polycert import make_certificate,verify as all_pairs
from n6.flat_octahedron import original_candidates,verify_fixed_tree
from n6.original_edge_rule import verify as budget_verify
from n6.cofacial_star_reduction import verify_case_A


class ComplementarySourceTests(unittest.TestCase):
    def setUp(self):set_precision(240)

    def test_new_sharp_pair_uses_its_own_case_A_tree_throughout_a_full_chart(self):
        for family in (False,True):
            s=specification(family=family);r=select(s)
            self.assertEqual(r['branch'],'complementary_two_angle_Case_A')
            self.assertTrue(r['fixed_tree_proof']['earlier_two_angle_condition'])
            self.assertEqual({v for v,b in r['curvature_comparisons_with_pi'].items() if b=='>'},{2,4})
            self.assertEqual(all_pairs(make_certificate({**s,'cut_edges':r['cut_edges']}))['result'],'verified')
            _,trees=original_candidates(s['faces'])
            for t in trees:
                with self.assertRaises(ValueError):verify_fixed_tree({**s,'cut_edges':t['cuts']})
                with self.assertRaises(ValueError):budget_verify({**s,'cut_edges':t['cuts']})

    def test_reflection_closes_the_other_previously_open_sharp_pair(self):
        s=specification('reflected');r=select(s)
        self.assertEqual(r['route_corner'],3)
        self.assertEqual({v for v,b in r['curvature_comparisons_with_pi'].items() if b=='>'},{3,5})
        self.assertEqual(all_pairs(make_certificate({**s,'cut_edges':r['cut_edges']}))['result'],'verified')

    def test_single_sharp_corner_equality_is_included(self):
        s=specification('boundary');r=select(s)
        self.assertEqual(r['curvature_comparisons_with_pi'][2],'=')
        self.assertTrue(all(b=='<' for v,b in r['curvature_comparisons_with_pi'].items() if v!=2))
        self.assertEqual(all_pairs(make_certificate({**s,'cut_edges':r['cut_edges']}))['result'],'verified')

    def test_last_singleton_fallback_and_reflection_replay_all_pairs(self):
        from n6.minus_edge_theorem import select as whole_select
        for kind,family,sharp in [('fallback',False,4),('fallback',True,4),('fallback_reflected',False,5)]:
            with self.subTest(kind=kind,family=family):
                s=specification(kind,family);r=whole_select(s)
                self.assertEqual(r['branch'],'failed_sharp_source_forces_complementary_gates')
                self.assertEqual(set(r['failed_direct_thresholds']),{sharp})
                c=r['fixed_tree_proof']
                self.assertEqual({v for v,b in c['curvature_comparisons_with_pi'].items() if b=='>'},{sharp})
                self.assertTrue(all(v=='>' for v in c['corner_gate_comparisons'].values()))
                self.assertEqual(all_pairs(make_certificate({**s,'cut_edges':r['cut_edges']}))['result'],'verified')

    def test_four_failed_routes_example_is_outside_the_corner_hypothesis(self):
        root=Path(__file__).resolve().parents[1]/'results'
        s=json.loads((root/'minus-cofacial-0-failure.certificate.json').read_text())
        with self.assertRaises(ValueError):select(s)


if __name__=='__main__':unittest.main()
