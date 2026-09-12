import json,unittest
from n7.bipyramid_adjacent import verify_identity,replay_saved,certify
from n7.bipyramid_morph import ROOT
class AdjacentChecks(unittest.TestCase):
    def test_exact_identity_and_two_realized_branches(self):
        self.assertEqual(verify_identity()['exact_integer_coefficient_identities'],33)
        r=replay_saved();self.assertEqual(r['exact_examples'],2)
        self.assertEqual(r['branches'],['ordered and short','switch to ordered and short'])
        for row in json.loads((ROOT/'results/bipyramid-adjacent.json').read_text())['examples']:
            n=row['certificate']['independent_net_check'];self.assertEqual(n['shared_vertex_pairs']+len(n['strict_separators']),45)
    def test_different_pattern_rejected(self):
        row=json.loads((ROOT/'results/bipyramid-receiver-pairs.json').read_text())['examples'][0]
        with self.assertRaises(ValueError):certify(row)
if __name__=='__main__':unittest.main()
