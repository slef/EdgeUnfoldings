import itertools
import json
from pathlib import Path
import unittest
import z3
from n6.certify import Geometry
from n6.curvature import angle_le,cmul,sum_angles_lt_pi,curvature_sum_lt_pi,curvature_sum_lt_angle,face_plus_curvature_lt_pi,verify_order

RAYS={1:(1,1),2:(0,1),3:(-1,1),4:(-1,0),5:(-1,-1),6:(0,-1),7:(1,-1)}


def truth(expr):return z3.is_true(z3.simplify(expr))


class CurvaturePredicateTests(unittest.TestCase):
    def test_sum_angle_order_including_pi_and_ties(self):
        for a,b in itertools.product(RAYS,repeat=2):
            self.assertEqual(truth(angle_le(RAYS[a],RAYS[b])),a<=b,(a,b))

    def test_sum_of_face_angles_tracks_full_turns(self):
        for n in range(1,7):
            for angles in itertools.product((1,2,3),repeat=n):
                self.assertEqual(truth(sum_angles_lt_pi([RAYS[a] for a in angles])),sum(angles)<4,angles)

    def test_curvature_sums_and_face_angle_boundaries(self):
        for a,b in itertools.product(RAYS,repeat=2):
            self.assertEqual(truth(curvature_sum_lt_pi(RAYS[a],RAYS[b])),16-a-b<4,(a,b))
            for q in (1,2,3):
                self.assertEqual(truth(curvature_sum_lt_angle(RAYS[a],RAYS[b],RAYS[q])),16-a-b<q,(a,b,q))
        for a,q in itertools.product(RAYS,(1,2,3)):
            self.assertEqual(truth(face_plus_curvature_lt_pi(RAYS[q],RAYS[a])),q+8-a<4,(a,q))

    def test_exact_sharpest_apex_in_D_counterexample(self):
        path=Path(__file__).resolve().parents[1]/'results/d-lemma-counterexample.json'
        g=Geometry(json.loads(path.read_text()))
        self.assertEqual(verify_order(g,[(3,i) for i in range(6) if i!=3])['result'],'verified_curvature_order')
        with self.assertRaises(ValueError):verify_order(g,[(0,3)])


if __name__=='__main__':unittest.main()
