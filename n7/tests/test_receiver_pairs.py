import json,unittest
from fractions import Fraction as F
from n7.bipyramid_morph import ROOT,I
from n7.angle_intervals import pi,atan,vector_angle
from n7.bipyramid_receiver_identity import verify
from n7.bipyramid_receiver_pairs import replay_saved,certify

class ReceiverPairChecks(unittest.TestCase):
    def test_twenty_exact_correction_identities(self):
        result=verify()
        self.assertEqual(result['identities'],20)
        self.assertTrue(all(not any(x['zero_residual']) for x in result['checks']))

    def test_rational_angle_reductions(self):
        p=pi();self.assertGreater(p.lo,I.bounds(F('3.1415926')).hi)
        self.assertLess(p.hi,I.bounds(F('3.1415927')).lo)
        a=atan(F(1,2))+atan(F(1,3));b=atan(1)
        self.assertLessEqual(a.lo,b.hi);self.assertLessEqual(b.lo,a.hi)
        a=atan(F(2));b=pi()/2-atan(F(1,2))
        self.assertLessEqual(a.lo,b.hi);self.assertLessEqual(b.lo,a.hi)
        for x in(F(-2),F(-1),F(-1,2),F(0),F(1,2),F(1),F(2)):
            a=atan(I.bounds(x,x+F(1,100)));b=atan(x);c=atan(x+F(1,100))
            self.assertLessEqual(a.lo,b.lo);self.assertGreaterEqual(a.hi,c.hi)

    def test_collinear_angle_check_is_rejected(self):
        a=[I.bounds(1),I.bounds(0)]
        with self.assertRaises(ValueError):vector_angle(a,a)

    def test_four_exact_chain_pair_examples(self):
        result=replay_saved();self.assertEqual(result['exact_examples'],4)
        self.assertEqual(result['branches'].count('Case A'),3)
        self.assertEqual(result['branches'].count('base cones'),1)
        rows=json.loads((ROOT/'results/bipyramid-receiver-pairs.json').read_text())['examples']
        gates=[r['certificate']['branch'].get('cap_correction_gate') for r in rows]
        self.assertIn(False,gates);self.assertIn(True,gates)
        for row in rows:
            c=row['certificate']['independent_net_check']
            self.assertEqual(c['fan_pairs']+len(c['strict_separators']),45)

    def test_incorrect_long_patch_is_rejected(self):
        row=json.loads((ROOT/'results/bipyramid-receiver-pairs.json').read_text())['examples'][0]
        row['long_patch']=3
        with self.assertRaises(ValueError):certify(row)

if __name__=='__main__':unittest.main()
