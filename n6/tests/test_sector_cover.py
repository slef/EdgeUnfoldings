import copy
import json
from pathlib import Path
import unittest
from n6.sector_cover import verify as verify_cover
from n6.polycert import point_spec,make_certificate,verify
from n6.intervals import set_precision
from n6.octa_patterns import FACES
from n6.convex_patches import classify
from n6.sector_audit import verify as verify_radial


class SectorCoverTests(unittest.TestCase):
    def setUp(self):
        set_precision(192)
        self.root=Path(__file__).resolve().parents[1]/'results'

    def test_certified_examples_in_all_five_patch_regimes(self):
        for name in ('zero','one','two-adjacent','two-opposite','three'):
            with self.subTest(regime=name):
                cert=json.loads((self.root/('short-edge-'+name+'.certificate.json')).read_text())
                report=verify_cover(cert)
                self.assertEqual(report['result'],'verified_short_edge_cover_hypotheses')
                self.assertEqual(verify(cert)['result'],'verified')
                self.assertEqual(classify(cert)['regime'],name)
                self.assertEqual(report['source'],1)
                self.assertTrue(report['candidate_slit_vertices'])

    def test_length_equality_is_accepted(self):
        p=[[0,0,0],[0,0,5],[3,0,1],[0,3,1],[-3,0,1],[0,-3,1]]
        spec=point_spec(p,FACES,[[0,u] for u in range(2,6)]+[[1,2]])
        spec['sector_cover']=dict(source=0,sector_vertex=1,equator=[2,3,4,5])
        result=verify_cover(spec)
        self.assertEqual(result['short_vertices'],[2,3,4,5])
        self.assertTrue(all(gap==['0','0'] for gap in result['squared_length_gaps'].values()))
        self.assertEqual(verify(make_certificate(spec))['result'],'verified')

    def test_high_curvature_vertex_need_not_be_globally_sharpest(self):
        cert=json.loads((self.root/'short-edge-two-opposite.certificate.json').read_text())
        cert['sector_cover'].update(source=0,sector_vertex=1)
        self.assertEqual(verify_cover(cert)['source'],0)

    def test_insufficient_curvature_is_rejected(self):
        cert=json.loads((self.root/'short-edge-one.certificate.json').read_text())
        cert['sector_cover'].update(source=0,sector_vertex=1)
        with self.assertRaisesRegex(ValueError,'curvature'):
            verify_cover(cert)

    def test_exact_three_patch_radial_obstruction_is_rejected(self):
        set_precision(240)
        cert=json.loads((self.root/'sector-three-patch-radial-failure.certificate.json').read_text())
        self.assertEqual(classify(cert)['regime'],'three')
        self.assertEqual(verify_radial(cert)['result'],'verified_failure_of_sharpest_sector_radial_test')
        self.assertEqual(verify(cert)['result'],'verified')
        cert['sector_cover']=dict(source=1,sector_vertex=0,equator=[2,3,4,5])
        with self.assertRaisesRegex(ValueError,'no certified short endpoint'):
            verify_cover(cert)

    def test_invalid_opposite_pair_is_rejected(self):
        cert=json.loads((self.root/'short-edge-one.certificate.json').read_text())
        cert['sector_cover']['source']=2
        with self.assertRaises(ValueError):verify_cover(cert)


if __name__=='__main__':unittest.main()
