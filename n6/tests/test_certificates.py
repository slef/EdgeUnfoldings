import copy
from fractions import Fraction as F
import json
from pathlib import Path
import unittest
from n6.intervals import I
from n6.certify import make_certificate, verify
from n6.audit_witness import verify_witness

RESULTS = Path(__file__).resolve().parents[1] / 'results'


class IntervalTests(unittest.TestCase):
    def test_outward_arithmetic_contains_rational_samples(self):
        a,b = I('-7/3','5/7'), I('1/11','3/5')
        for x in [F(-7,3), F(-1,3), F(0), F(5,7)]:
            for y in [F(1,11), F(2,7), F(3,5)]:
                for val, interval in [(x+y,a+b),(x-y,a-b),(x*y,a*b),(x/y,a/b)]:
                    self.assertLessEqual(interval.lo,val)
                    self.assertGreaterEqual(interval.hi,val)

    def test_square_and_sqrt_boundaries(self):
        self.assertEqual(I(-2,3).square(),I(0,9))
        for q in [F(0),F(1),F(2),F(1,3),F(123456789,53),F(1,10**70)]:
            r=I(q).sqrt()
            self.assertLessEqual(r.lo*r.lo,q)
            self.assertGreaterEqual(r.hi*r.hi,q)
        self.assertEqual(I(4).sqrt(),I(2))

    def test_invalid_operations_rejected(self):
        for operation in [lambda:I(0.1),lambda:I(2,1),lambda:I(1)/I(-1,1),lambda:I(-1).sqrt()]:
            with self.assertRaises((TypeError,ValueError)):
                operation()


class CertificateTests(unittest.TestCase):
    def setUp(self):
        self.cert=json.loads((RESULTS/'octahedron-box.certificate.json').read_text())

    def test_explicit_open_box(self):
        result=verify(self.cert)
        self.assertEqual(result['pairs'],{'vertex_fan':19,'separating_edge':9})
        self.assertTrue(all(F(q[0]) < F(q[1]) for p in self.cert['coordinate_box'] for q in p))

    def test_report_uses_the_current_interval_precision(self):
        from n6.intervals import BITS, set_precision
        try:
            for precision in (64, 240):
                set_precision(precision)
                self.assertIn(f'{precision} fractional bits', verify(self.cert)['arithmetic'])
        finally:
            set_precision(BITS)

    def test_every_pair_required_once(self):
        for witnesses in [self.cert['pair_witnesses'][:-1],self.cert['pair_witnesses']+[self.cert['pair_witnesses'][0]]]:
            bad={**self.cert,'pair_witnesses':witnesses}
            with self.assertRaises(ValueError):verify(bad)

    def test_false_separator_rejected(self):
        bad=copy.deepcopy(self.cert)
        w=next(w for w in bad['pair_witnesses'] if w['kind']=='separating_edge')
        w['edge'].reverse()
        with self.assertRaises(ValueError):verify(bad)

    def test_false_vertex_copy_rejected(self):
        bad=copy.deepcopy(self.cert)
        w=next(w for w in bad['pair_witnesses'] if w['kind']=='vertex_fan')
        w['vertex']=10
        with self.assertRaises(ValueError):verify(bad)

    def test_invalid_polyhedra_and_cuts_rejected(self):
        for field,value in [('cut_edges',[[0,1]]*5),('faces',self.cert['faces'][:-1]),
                            ('coordinate_box',[[['-100','100']]*3]*6)]:
            with self.assertRaises(ValueError):verify({**self.cert,field:value})

    def test_similarity_preserves_box_certificate(self):
        transformed=copy.deepcopy(self.cert)
        # Uniform scale 3, translate, reflect z; reverse all faces to keep outward orientation.
        transformed['coordinate_box']=[[[str(3*F(q[0])+7),str(3*F(q[1])+7)] if j<2 else
                                       [str(-3*F(q[1])+7),str(-3*F(q[0])+7)] for j,q in enumerate(p)]
                                     for p in transformed['coordinate_box']]
        transformed['faces']=[f[::-1] for f in transformed['faces']]
        self.assertEqual(verify(make_certificate(transformed))['result'],'verified')

    def test_exact_counterexample_to_supporting_lemma(self):
        spec=json.loads((RESULTS/'d-lemma-counterexample.json').read_text())
        self.assertTrue(verify_witness(spec)['result'].startswith('verified_counterexample'))
        bad=copy.deepcopy(spec)
        bad['halfplane_claim']['far_equator']=bad['halfplane_claim']['shared_equator']
        with self.assertRaises(ValueError):verify_witness(bad)


if __name__=='__main__':unittest.main()
