import json,unittest
from n7.bipyramid_morph import ROOT
from n7.bipyramid_radial import replay_saved,certify_local,certify_rule
class RadialChecks(unittest.TestCase):
    def test_both_lemmas_and_all_projection_cases(self):
        r=replay_saved();self.assertEqual(r['exact_local_examples'],4);self.assertEqual(r['exact_rule_examples'],5)
        self.assertEqual(r['projection_regimes'],['first endpoint','interior','second endpoint'])
        rows=json.loads((ROOT/'results/bipyramid-radial.json').read_text())['rule_examples']
        self.assertEqual({r['certificate']['pattern'] for r in rows},{'FCCBC','FCFCC','FCCCB'})
        for row in rows:
            n=row['certificate']['independent_net_check'];self.assertEqual(n['shared_vertex_pairs']+len(n['strict_separators']),45)
    def test_short_extension_cannot_supply_radial_lemma(self):
        row=json.loads((ROOT/'results/bipyramid-radial.json').read_text())['local_examples'][0]
        row['fan_pole']=11-row['fan_pole']
        with self.assertRaises(ValueError):certify_local(row)
if __name__=='__main__':unittest.main()
