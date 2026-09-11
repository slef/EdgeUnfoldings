import copy
import unittest
from n6.intervals import set_precision
from n6.polycert import Geometry,make_certificate,verify as all_pairs
from n6.curvature import verify_order,angle_product,interval_angle_le
from n6.source_choice import verify
from n6.source_choice_examples import specification
from n6.selected_octahedron_examples import specification as selected_spec


class SourceChoiceTests(unittest.TestCase):
    def setUp(self):set_precision(240)

    def test_low_source_less_sharp_than_fan(self):
        cert=make_certificate(specification('low'));report=verify(cert)
        self.assertTrue(report['all_curvatures_at_most_pi'])
        self.assertFalse(report['source_curvature_at_least_pi'])
        self.assertEqual(all_pairs(cert)['result'],'verified')
        g=Geometry(cert);verify_order(g,[(1,0)])
        self.assertIs(interval_angle_le(angle_product(g.p,g.faces,g.h,0),angle_product(g.p,g.faces,g.h,1)),False)
        with self.assertRaises(ValueError):verify_order(g,[(0,1)])

    def test_high_source_need_not_be_sharpest(self):
        cert=make_certificate(specification('high'));report=verify(cert)
        self.assertTrue(report['source_curvature_at_least_pi'])
        self.assertFalse(report['all_curvatures_at_most_pi'])
        self.assertEqual(all_pairs(cert)['result'],'verified')
        with self.assertRaises(ValueError):verify_order(Geometry(cert),[(0,1)])

    def test_equality_and_ties(self):
        self.assertTrue(verify(selected_spec('curvature-equality'))['source_curvature_at_least_pi'])
        self.assertTrue(verify(selected_spec('regular-ties'))['all_curvatures_at_most_pi'])

    def test_invalid_source_condition_and_orientation(self):
        spec=specification('high')
        # Re-root at a low-curvature equator vertex while the poles exceed pi.
        from n6.point_audit import exact_hull,cuts_for
        points=[[int(c[0][0]) for c in p] for p in spec['coordinate_polynomials']]
        faces,adj=exact_hull(points);v,w=2,4;nxt={}
        for f in faces:
            if w in f:
                j=f.index(w);nxt[f[(j+1)%3]]=f[(j+2)%3]
        ring=[1]
        while len(ring)<4:ring.append(nxt[ring[-1]])
        spec['selection']=dict(apex=v,antipode=w,equator=ring,slit_index=0)
        spec['cut_edges']=[list(e) for e in cuts_for(v,1,adj)]
        with self.assertRaisesRegex(ValueError,'Neither source-choice'):verify(spec)
        spec=copy.deepcopy(specification('low'));spec['selection']['equator'].reverse()
        with self.assertRaises(ValueError):verify(spec)


if __name__=='__main__':unittest.main()
