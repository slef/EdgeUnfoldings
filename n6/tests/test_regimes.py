from copy import deepcopy
import itertools
import json
from pathlib import Path
import unittest
from n6.intervals import I
from n6.regimes import curvature_sum_band,two_curvatures_angle,face_plus_curvature_pi,positive_angles_pi,verify

RAYS={1:(1,1),2:(0,1),3:(-1,1),4:(-1,0),5:(-1,-1),6:(0,-1),7:(1,-1)}
RAYS={k:tuple(map(I,v)) for k,v in RAYS.items()}


def comparison(a,b):return '<' if a<b else '>' if a>b else '='


class AngularRegimeTests(unittest.TestCase):
    def test_curvature_sum_including_pi_two_pi_and_large_wrap(self):
        for a,b in itertools.product(RAYS,repeat=2):
            k=16-a-b
            expected='K<pi' if k<4 else 'K=pi' if k==4 else 'pi<K<2pi' if k<8 else 'K=2pi' if k==8 else 'K>2pi'
            self.assertEqual(curvature_sum_band(RAYS[a],RAYS[b]),expected,(a,b))
            for q in (1,2,3):
                self.assertEqual(two_curvatures_angle(RAYS[a],RAYS[b],RAYS[q]),comparison(k,q),(a,b,q))

    def test_D_regime_all_quarter_rays(self):
        for a,q in itertools.product(RAYS,(1,2,3)):
            self.assertEqual(face_plus_curvature_pi(RAYS[q],RAYS[a]),comparison(q+8-a,4),(a,q))

    def test_positive_sums_cannot_wrap_back_into_small_regime(self):
        for n in range(1,6):
            for seq in itertools.product((1,2,3),repeat=n):
                self.assertEqual(positive_angles_pi([RAYS[q] for q in seq]),comparison(sum(seq),4),seq)

    def test_exact_large_D_example_under_both_rankings(self):
        cert=json.loads((Path(__file__).resolve().parents[1]/'results/caseB-large-D.certificate.json').read_text())
        result=verify(cert)
        self.assertEqual(result['triples'][1]['left_D_comparison'],'>')
        self.assertEqual(result['triples'][1]['case_A_comparison'],'>')
        bad=deepcopy(cert);bad['angular_claims']['triples'][1]['left_D_comparison']='<'
        with self.assertRaisesRegex(ValueError,'Angular claim'):verify(bad)
        bad=deepcopy(cert);bad['angular_claims']['triples'][1].pop('left_D_comparison')
        with self.assertRaisesRegex(ValueError,'Incomplete angular'):verify(bad)


if __name__=='__main__':unittest.main()
