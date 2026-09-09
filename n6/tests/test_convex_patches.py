import copy
import json
from pathlib import Path
import unittest
from n6.convex_patches import classify
from n6.polycert import point_spec, verify, make_certificate
from n6.intervals import set_precision
from n6.octa_patterns import FACES


class ConvexPatchTests(unittest.TestCase):
    def setUp(self):
        set_precision(192)
        self.root = Path(__file__).resolve().parents[1]/'results'

    def test_five_exact_regimes_and_certified_nets(self):
        for regime in ('zero','one','two-adjacent','two-opposite','three'):
            with self.subTest(regime=regime):
                cert = json.loads((self.root/('octa-patches-'+regime+'.certificate.json')).read_text())
                result = classify(cert)
                self.assertEqual(result['regime'], regime)
                self.assertEqual(verify(cert)['result'], 'verified')
                if regime == 'one':
                    self.assertIn('Whole-net success remains open',result['conclusion'])
                    i, = result['nonconvex_patches']
                    self.assertEqual(result['candidate_slit_indices'], [(i+2)%4,(i+3)%4])
                    self.assertIn(next(u for w,u in cert['cut_edges'] if w==1), result['candidate_slit_vertices'])
                elif regime == 'zero':
                    # The theorem asserts every slit, so independently certify
                    # the three choices absent from the saved example too.
                    for u in range(2,6):
                        alternate = copy.deepcopy(cert)
                        alternate['cut_edges'] = [[0,x] for x in range(2,6)]+[[1,u]]
                        self.assertEqual(verify(make_certificate(alternate))['result'], 'verified')
                else:
                    self.assertEqual(result['candidate_slit_indices'], [])

    def test_false_sharpest_apex_hypothesis_is_rejected(self):
        cert = json.loads((self.root/'octa-patches-one.certificate.json').read_text())
        cert['selection']['apex'],cert['selection']['antipode'] = 1,0
        with self.assertRaises(ValueError):
            classify(cert)

    def test_wrong_equator_order_is_rejected(self):
        cert = json.loads((self.root/'octa-patches-one.certificate.json').read_text())
        cert['selection']['equator'] = [2,4,3,5]
        with self.assertRaises(ValueError):
            classify(cert)

    def test_tied_curvature_and_symmetric_convex_patches(self):
        spec = point_spec([[0,0,1],[0,0,-1],[1,0,0],[0,-1,0],[-1,0,0],[0,1,0]], FACES,
                          [[0,u] for u in range(2,6)]+[[1,2]])
        spec['selection'] = dict(apex=0,antipode=1,equator=[2,3,4,5])
        self.assertEqual(classify(spec)['regime'], 'zero')

    def test_straight_corner_is_included_in_convex_case(self):
        spec = point_spec([[0,0,1],[0,0,-1],[1,0,0],[1,-1,0],[-1,-1,0],[-1,1,0]], FACES,
                          [[0,u] for u in range(2,6)]+[[1,2]])
        spec['selection'] = dict(apex=0,antipode=1,equator=[2,3,4,5])
        result = classify(spec)
        self.assertEqual(result['patches'][0]['corner_relations_to_pi'], ['=','<'])
        self.assertEqual(result['regime'], 'zero')
        self.assertFalse(result['sharpest_apex_required'])
        self.assertEqual(verify(make_certificate(spec))['result'], 'verified')


if __name__ == '__main__':
    unittest.main()
