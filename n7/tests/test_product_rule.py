import json,unittest
from n7.bipyramid_product_rule import certify,replay_saved
from n7.bipyramid_morph import ROOT
class ProductRuleChecks(unittest.TestCase):
    def test_exact_successes_and_genuine_two_pole_conflicts(self):
        self.assertEqual(replay_saved(),{'exact_examples':9,'applications':2,'two_pole_test_failures':7})
        rows=json.loads((ROOT/'results/bipyramid-product-rule.json').read_text())['examples']
        for row in rows[:2]:
            n=row['certificate']['independent_net_check'];self.assertEqual(n['shared_vertex_pairs']+len(n['strict_separators']),45)
        c=rows[1]['certificate'];self.assertEqual(c['good_sources'],[5,6]);self.assertFalse(any(c['inward_corner_plane_passes'].values()))
        for row in rows[2:]:
            c=row['certificate'];self.assertTrue(all(c['strictly_failed_vertices'].values()))
            witnesses=[c['failed_corner_neighbors'][str(q)][0] for q in (5,6)]
            self.assertEqual(len({v for w in witnesses for v in (w['corner'],w['neighbor'])}),4)
        for row in rows[-3:]:
            self.assertEqual(len(row['certificate']['independent_safe_maximal_slit_nets']),2)
            for n in row['certificate']['independent_safe_maximal_slit_nets']:self.assertEqual(n['shared_vertex_pairs']+len(n['strict_separators']),45)
    def test_failed_condition_cannot_be_claimed_success(self):
        row=json.loads((ROOT/'results/bipyramid-product-rule.json').read_text())['examples'][2]
        del row['expect_both_tests_fail']
        with self.assertRaisesRegex(ValueError,'No source certified'):certify(row)
if __name__=='__main__':unittest.main()
