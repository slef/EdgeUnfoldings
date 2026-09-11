import unittest
from n6.intervals import I,set_precision
from n6.slit_threshold import verify,weighted_slit_pi
from n6.slit_threshold_examples import specification,check_nonmaximum_slit
from n6.selected_octahedron_examples import specification as selected_spec
from n6.low_local_failure import specification as failure_spec
from n6.polycert import Geometry,make_certificate,verify as all_pairs
from n6.curvature import angle_product


class SlitThresholdTests(unittest.TestCase):
    def setUp(self):set_precision(240)

    def test_nonmaximum_slits_in_both_source_branches(self):
        for name in ('low','high','low-family','high-family'):
            with self.subTest(name=name):
                cert=make_certificate(specification(name));report=verify(cert)
                self.assertTrue(report['whole_net_nonoverlapping'])
                self.assertFalse(report['R_required'])
                self.assertFalse(report['every_slit_lemma_F_proved'])
                self.assertTrue(check_nonmaximum_slit(cert)['strictly_sharper_equator_vertices'])
                self.assertEqual(report['source_curvature_at_least_pi'],name.startswith('high'))
                self.assertEqual(all_pairs(cert)['result'],'verified')

    def test_exact_weighted_angle_boundary_and_uncertainty(self):
        # Synthetic exact phase products test the comparator, not existence
        # of a convex polyhedron with these particular prescribed curvatures.
        c=(I(1),I(-1));w=(I(0),I(-1)) # curvatures pi/4 and pi/2
        self.assertEqual(weighted_slit_pi(c,w),'=')
        self.assertEqual(weighted_slit_pi((I(2),I(-1)),w),'<')
        self.assertEqual(weighted_slit_pi((I(1),I(-2)),w),'>')
        self.assertIsNone(weighted_slit_pi(c,(I('-1/1000','1/1000'),I(-1))))
        self.assertEqual(weighted_slit_pi(c,(I(-1),I(0))),'>')

    def test_source_equality_and_ties(self):
        self.assertTrue(verify(selected_spec('curvature-equality'))['source_curvature_at_least_pi'])
        self.assertTrue(verify(selected_spec('regular-ties'))['whole_net_nonoverlapping'])

    def test_failure_of_threshold_can_be_safe_or_overlapping(self):
        for spec in (specification('safe-below-threshold'),failure_spec()):
            g=Geometry(spec);s=spec['selection'];c=s['equator'][s['slit_index']]
            totals={x:angle_product(g.p,g.faces,g.h,x) for x in (c,s['antipode'])}
            self.assertEqual(weighted_slit_pi(totals[c],totals[s['antipode']]),'<')
            with self.assertRaisesRegex(ValueError,'Weighted slit threshold'):verify(spec)
        self.assertEqual(all_pairs(make_certificate(specification('safe-below-threshold')))['result'],'verified')


if __name__=='__main__':unittest.main()
