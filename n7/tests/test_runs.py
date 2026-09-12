import json,unittest
from n7.bipyramid_runs import certify,replay_saved
from n7.bipyramid_morph import ROOT
class OrderedRunChecks(unittest.TestCase):
    def test_three_and_four_inward_examples(self):
        r=replay_saved();self.assertEqual(r['run_lengths'],[3,4,4])
        for row in json.loads((ROOT/'results/bipyramid-runs.json').read_text())['examples']:
            c=row['certificate'];self.assertTrue(c['both_poles_below_pi'])
            n=c['independent_net_check'];self.assertEqual(n['shared_vertex_pairs']+len(n['strict_separators']),45)
        first=json.loads((ROOT/'results/bipyramid-runs.json').read_text())['examples'][0]
        self.assertEqual(first['certificate']['good_fans'],[5])
    def test_other_pattern_rejected(self):
        row=json.loads((ROOT/'results/bipyramid-adjacent.json').read_text())['examples'][0]
        with self.assertRaises(ValueError):certify(row)
if __name__=='__main__':unittest.main()
