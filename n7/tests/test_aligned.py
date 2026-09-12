import json,unittest
from n7.bipyramid_aligned import ROOT,certify,replay_saved

class AlignedChecks(unittest.TestCase):
    def rows(self):return json.loads((ROOT/'results/bipyramid-aligned.json').read_text())['examples']
    def test_both_completion_regimes_and_equal_heights(self):
        r=replay_saved();self.assertEqual(r['exact_examples'],7)
        self.assertEqual(set(r['completion_branches']),{'complete the missing gap','fan already convex'})
        rows=self.rows();self.assertTrue(any(row['certificate']['squared_auxiliary_height']=='0' for row in rows))
        self.assertEqual(sum(row['certificate']['pattern']=='CBBBB' for row in rows),2)
        for row in rows:
            n=row['certificate']['independent_net_check'];self.assertEqual(len(n['shared_vertex_pairs'])+len(n['strict_separators']),45)
    def test_full_coordinate_box_and_excessive_box_rejection(self):
        from fractions import Fraction
        from n7.bipyramid_four_bad_box import replay_saved,certify
        r=replay_saved();self.assertEqual(r['independent_coordinate_intervals'],21)
        self.assertEqual(r['shared_vertex_pairs']+r['strict_interval_separators'],45)
        with self.assertRaises(ValueError):certify(Fraction(1,100))
    def test_displaced_pole_is_outside_the_checker_scope(self):
        row=self.rows()[0];row['points'][6][0]+=.001
        with self.assertRaises(ValueError):certify(row)
    def test_wrong_height_order_is_rejected(self):
        row=self.rows()[0];row['fan_pole']=6
        with self.assertRaises(ValueError):certify(row)
    def test_nonmaximal_slit_is_rejected(self):
        row=self.rows()[0];row['slit']=1
        with self.assertRaises(ValueError):certify(row)

if __name__=='__main__':unittest.main()
