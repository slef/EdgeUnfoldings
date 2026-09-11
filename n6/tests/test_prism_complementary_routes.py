import unittest
from n6.intervals import set_precision
from n6.prism_complementary_examples import specification
from n6.prism_complementary_routes import select
from n6.polycert import make_certificate,verify as all_pairs
from n6.flat_octahedron import original_candidates,verify_fixed_tree
from n6.original_edge_rule import verify as budgets
from n6.prism_two_sharp_ends import specification as two_sharp


class ComplementaryPrismTests(unittest.TestCase):
    def setUp(self):set_precision(240)

    def test_new_point_full_chart_and_reflection_replay_original_pairs(self):
        for family,reflected,sharp in [(False,False,0),(True,False,0),(False,True,4)]:
            with self.subTest(family=family,reflected=reflected):
                s=specification(family,reflected);r=select(s)
                self.assertEqual(r['branch'],'complementary_route_Case_B')
                self.assertEqual({v for v,b in r['curvature_comparisons_with_pi'].items() if b=='>'},{sharp})
                self.assertFalse(r['full_prism_proved'])
                self.assertEqual(all_pairs(make_certificate({**s,'cut_edges':r['cut_edges']}))['result'],'verified')
                _,trees=original_candidates(s['faces'])
                for t in trees:
                    with self.assertRaises(ValueError):verify_fixed_tree({**s,'cut_edges':t['cuts']})
                    with self.assertRaises(ValueError):budgets({**s,'cut_edges':t['cuts']})

    def test_rejects_the_distinct_two_high_fan_family(self):
        with self.assertRaises(ValueError):select(two_sharp())


if __name__=='__main__':unittest.main()
