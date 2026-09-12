import json,unittest
from n7.bipyramid_chain_rule import certify,replay_saved
from n7.bipyramid_morph import ROOT

class ChainRuleChecks(unittest.TestCase):
    def test_exact_rule_and_all_face_pairs(self):
        report=replay_saved();self.assertEqual(report['exact_examples'],6)
        self.assertEqual(report['branches'],['both short','opposing long extensions','switch to both short'])
        rows=json.loads((ROOT/'results/bipyramid-chain-rule.json').read_text())['examples']
        longs=set()
        for row in rows:
            c=row['certificate'];n=c['independent_net_check']
            self.assertEqual(n['shared_vertex_pairs']+len(n['strict_separators']),45)
            longs.update(x['bad_patch'] for x in c['long_receiver_bounds'])
        self.assertEqual(longs,{0,3})
    def test_wrong_pattern_rejected(self):
        row={'points':[[1,0,0],[.6,.8,0],[-.6,.8,0],[-1,0,0],[0,-1,0],[0,0,1],[0,0,-1]]}
        with self.assertRaises(ValueError):certify(row)
if __name__=='__main__':unittest.main()
