import json,unittest
from n7.bipyramid_product_rule import certify,replay_saved
from n7.bipyramid_morph import ROOT
class ProductRuleChecks(unittest.TestCase):
    def test_exact_successes_and_genuine_two_pole_conflicts(self):
        self.assertEqual(replay_saved(),{'exact_examples':6,'applications':2,'two_pole_test_failures':4})
        rows=json.loads((ROOT/'results/bipyramid-product-rule.json').read_text())['examples']
        for row in rows[:2]:
            n=row['certificate']['independent_net_check'];self.assertEqual(n['shared_vertex_pairs']+len(n['strict_separators']),45)
        c=rows[1]['certificate'];self.assertEqual(c['good_sources'],[5,6]);self.assertFalse(any(c['inward_corner_plane_passes'].values()))
        for row in rows[2:]:self.assertTrue(all(row['certificate']['strictly_failed_vertices'].values()))
    def test_failed_condition_cannot_be_claimed_success(self):
        row=json.loads((ROOT/'results/bipyramid-product-rule.json').read_text())['examples'][2]
        del row['expect_both_tests_fail']
        with self.assertRaisesRegex(ValueError,'No source certified'):certify(row)
if __name__=='__main__':unittest.main()
