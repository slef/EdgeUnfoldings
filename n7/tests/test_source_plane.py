import json,unittest
from fractions import Fraction
from n7.bipyramid_source_plane import certify,replay_saved
from n7.bipyramid_morph import ROOT
class SourcePlaneChecks(unittest.TestCase):
    def test_exact_low_pole_families_and_boundary(self):
        r=replay_saved();self.assertEqual(r['exact_examples'],8)
        rows=json.loads((ROOT/'results/bipyramid-source-plane.json').read_text())['examples']
        for row in rows:
            c=row['certificate'];n=c['independent_net_check'];self.assertEqual(n['shared_vertex_pairs']+len(n['strict_separators']),45)
        self.assertTrue(all(row['certificate']['both_poles_below_pi'] for row in rows[:7]))
        self.assertIn('0',rows[-1]['certificate']['source_plane_margins'])
    def test_opposite_pole_does_not_automatically_pass(self):
        row=json.loads((ROOT/'results/bipyramid-source-plane.json').read_text())['examples'][0]
        row['source']=11-row['source']
        with self.assertRaisesRegex(ValueError,'beyond the source plane'):certify(row)
if __name__=='__main__':unittest.main()
