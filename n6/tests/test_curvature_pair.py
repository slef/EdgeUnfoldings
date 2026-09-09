import copy,json,itertools
from pathlib import Path
import unittest
from n6.curvature_pair import verify as verify_pair,verify_central,weighted_curvature_bound
from n6.polycert import verify,point_spec
from n6.intervals import I,set_precision
from n6.octa_patterns import FACES


class CurvaturePairTests(unittest.TestCase):
    def setUp(self):
        set_precision(192);self.root=Path(__file__).resolve().parents[1]/'results'

    def test_weighted_comparison_including_wraps_and_equalities(self):
        rays={1:(1,1),2:(0,1),3:(-1,1),4:(-1,0),5:(-1,-1),6:(0,-1),7:(1,-1)}
        for a,b in itertools.product(rays,repeat=2):
            A=tuple(map(I,rays[a]));B=tuple(map(I,rays[b]))
            # Incident sums are a*pi/4 and b*pi/4; the curvatures
            # are their complements in 2*pi.
            expected=(8-a)+2*(8-b)>=8
            self.assertEqual(weighted_curvature_bound(A,B),expected,(a,b))

    def test_exact_instances_and_independent_nets(self):
        for name in ('zero','one','two-adjacent','two-opposite'):
            with self.subTest(regime=name):
                c=json.loads((self.root/('curvature-pair-'+name+'.certificate.json')).read_text())
                self.assertEqual(verify_pair(c)['result'],'verified_curvature_pair_hypotheses')
                self.assertEqual(verify(c)['result'],'verified')

    def test_insufficient_opposite_curvature_is_rejected(self):
        c=json.loads((self.root/'octa-patches-three.certificate.json').read_text())
        c['curvature_pair']=dict(sector_vertex=0,source=1,equator=[2,3,4,5])
        with self.assertRaisesRegex(ValueError,'Weighted curvature'):verify_pair(c)

    def test_whole_affine_central_region(self):
        c=json.loads((self.root/'central-octahedron-family.certificate.json').read_text())
        self.assertEqual(len(c['parameter_box']),9)
        self.assertEqual(verify_central(c)['result'],'verified_central_octahedron_hypotheses')
        self.assertEqual(verify(c)['result'],'verified')

    def test_broken_central_identity_is_rejected(self):
        c=json.loads((self.root/'central-octahedron-family.certificate.json').read_text())
        c['coordinate_polynomials'][1][0][0][0]='-20001/10000'
        with self.assertRaisesRegex(ValueError,'midpoints'):verify_central(c)

    def test_regular_octahedron_without_resolving_curvature_ties(self):
        p=[[0,0,1],[0,0,-1],[1,0,0],[0,-1,0],[-1,0,0],[0,1,0]]
        c=point_spec(p,FACES,[[0,u] for u in range(2,6)]+[[1,2]])
        self.assertEqual(verify_central(c)['result'],'verified_central_octahedron_hypotheses')


if __name__=='__main__':unittest.main()
