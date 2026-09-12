"""Verifier checks, including rejected near/invalid inputs; no sampling theorem."""
from fractions import Fraction as F
import itertools
import json
import unittest
from n7.a992_exact import I,S,ROOT,T,T_OTHER,certificate,geometry,develop,inside,replay_saved

class A992Checks(unittest.TestCase):
    def test_exact_certificates_replay(self):
        r=replay_saved()
        self.assertEqual(r['certified_overlap_tests'],5)
        self.assertEqual(r['certified_successful_nets'],4)
        self.assertEqual(r['universal_graph_status'],'open')
    def test_invalid_or_uncertain_certificates_are_rejected(self):
        c=json.loads((ROOT/'results/a992-exact-counterexample.json').read_text())
        q=c['geometry']['parameters'];w=list(map(F,c['interior_witness']))
        with self.assertRaises(ValueError):certificate(q,witness=[F(99),F(99)])
        with self.assertRaises(ValueError):certificate(q,witness=w,epsilon=F(1,10000))
        invalid=q.copy();invalid[8]='0'
        with self.assertRaises(ValueError):geometry(invalid)
        p,_=geometry(q)
        with self.assertRaises(ValueError):develop(p,T[:-1])
        # A vertex is not a *strict* interior witness even when boundaries touch.
        net=develop(p,T)
        with self.assertRaises(ValueError):inside(net[0],[F(0),F(0)])
    def test_localization_and_metric_preservation(self):
        c=json.loads((ROOT/'results/a992-exact-counterexample.json').read_text())
        q=list(map(F,c['geometry']['parameters']));p,_=geometry(q);n=develop(p,T)
        changed=q.copy();changed[2]+=F(1,1000000);changed[5]-=F(1,1000000)
        pp,_=geometry(changed);nn=develop(pp,T)
        self.assertEqual(n[0],nn[0]);self.assertEqual(n[1],nn[1])
        from n7.a992_exact import FACES,points
        exact=points(q)
        for f,poly in zip(FACES,n):
            for i,j in itertools.combinations(range(len(f)),2):
                target=sum((exact[f[i]][k]-exact[f[j]][k])**2 for k in range(3))
                got=sum((poly[i][k].mid()-poly[j][k].mid())**2 for k in range(2))
                self.assertAlmostEqual(got,float(target),places=11)
    def test_outward_rounding_of_nonlinear_arithmetic(self):
        def contains(i,x):return F(i.lo,S)<=x<=F(i.hi,S)
        for a,b in itertools.product([F(-7,3),F(-1,7),F(2,3),F(11,13)],repeat=2):
            self.assertTrue(contains(I.bounds(a)*I.bounds(b),a*b))
            self.assertTrue(contains(I.bounds(a)/I.bounds(b),a/b))
        sqrt2=I.bounds(2).sqrt()
        self.assertLessEqual(F(sqrt2.lo,S)**2,2)
        self.assertGreaterEqual(F(sqrt2.hi,S)**2,2)
        with self.assertRaises(ValueError):I.bounds(1)/I.bounds(-1,1)
        with self.assertRaises(ValueError):I.bounds(-1).sqrt()

if __name__=='__main__':unittest.main()
