"""Check the new identity and the geometric reduction's finite implementation."""
from fractions import Fraction as F
import itertools
import json
import unittest
import numpy as np
from n7.a992_exact import ROOT,points,sub,cross,dot
from n7.a992 import points_from_parameters,unfold
from n7.r0_identity import FACES,verify

class R0Checks(unittest.TestCase):
    def test_exact_positive_identity(self):
        report=verify()
        self.assertFalse(any(report['zero_residual']))
        self.assertEqual(report,json.loads((ROOT/'results/a992-r0-angle-identity.json').read_text()))

    def test_exact_narrow_fan_example(self):
        from n7.r0_examples import replay
        report=replay()
        self.assertTrue(report['strict_Left_overlap'])
        self.assertEqual(report['strict_branch_signs'],4)
        self.assertEqual(report['strict_Right_residual_separators'],3)

    def test_auxiliary_hull_and_pair_localization(self):
        right=((0,3),(0,4),(0,6),(1,3),(2,3),(3,5))
        aux_cut=((0,3),(0,5),(0,6),(1,3))
        for name in ('a992-exact-counterexample.json','a992-length-rule-counterexample.json',
                     'a992-corner-six-counterexample.json'):
            cert=json.loads((ROOT/'results'/name).read_text())
            q=list(map(F,cert['geometry']['parameters']));p=points(q)
            # Exact supporting-plane checks at these rational examples only.
            for face in FACES:
                a,b,c=[p[v] for v in face];normal=cross(sub(b,a),sub(c,a))
                values=[dot(normal,sub(p[v],a)) for v in (0,1,3,5,6) if v not in face]
                self.assertTrue(all(x>0 for x in values) or all(x<0 for x in values))
            # The different root frames disappear in cross-face distances.
            pp=points_from_parameters(list(map(float,q)))
            full=unfold(pp,right);aux=unfold(pp,aux_cut,FACES,4)
            for i,j in itertools.product(range(3),repeat=2):
                # Full face 135 and auxiliary face 153 have reversed final order.
                jj=(0,2,1)[j]
                d1=float(np.sum((full[1][i]-full[3][j])**2))
                d2=float(np.sum((aux[0][i]-aux[5][jj])**2))
                self.assertAlmostEqual(d1,d2,delta=1e-10*max(1.,d1,d2))

if __name__=='__main__':unittest.main()
