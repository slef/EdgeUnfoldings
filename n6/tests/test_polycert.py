import copy
from fractions import Fraction as F
import json
from pathlib import Path
import unittest
from n6.intervals import I
from n6.polynomials import Poly
from n6.polycert import Geometry,make_certificate,verify,verify_overlap,point_spec

RESULTS=Path(__file__).resolve().parents[1]/'results'


def read(name):return json.loads((RESULTS/name).read_text())


class PolynomialCertificateTests(unittest.TestCase):
    def test_polynomial_identity_and_interval_containment(self):
        x,y=Poly.variable(2,0),Poly.variable(2,1)
        self.assertTrue(((x+y)*(x-y)-x*x+y*y).is_zero())
        p=(x+y)*(x-y)
        box=[I('-2','3'),I('1/3','2/3')];bound=p.evaluate(box)
        for a in [F(-2),F(1,7),F(3)]:
            for b in [F(1,3),F(1,2),F(2,3)]:
                value=(a+b)*(a-b)
                self.assertLessEqual(bound.lo,value);self.assertGreaterEqual(bound.hi,value)
        self.assertEqual(Poly(2,p.json()).terms,p.terms)

    def test_nine_parameter_region_with_original_quadrilaterals(self):
        cert=read('prism-region.certificate.json');report=verify(cert)
        self.assertEqual(report['parameter_dimension'],9)
        self.assertEqual(report['facet_sizes'].count(4),2)
        self.assertEqual(sum(report['pairs'].values()),15)

    def test_false_coplanarity_is_rejected_symbolically(self):
        cert=read('prism-region.certificate.json')
        cert['coordinate_polynomials'][3][1].append(['1/10',[0]*9])
        with self.assertRaisesRegex(ValueError,'coplanarity'):Geometry(cert)

    def test_omitted_face_pair_is_not_a_complete_certificate(self):
        cert=read('prism-region.certificate.json');cert['pair_witnesses'].pop()
        with self.assertRaisesRegex(ValueError,'Missing face pairs'):verify(cert)

    def test_fixed_prism_tree_failure_and_successful_alternative(self):
        bad=read('prism-two-pair-failure.certificate.json')
        good=read('prism-alternative.certificate.json')
        self.assertEqual(verify_overlap(bad)['strict_signs'],8)
        self.assertEqual(verify(good)['result'],'verified')
        bad['cut_edges']=good['cut_edges']
        with self.assertRaises(ValueError):verify_overlap(bad)

    def test_missing_overlap_axis_is_rejected(self):
        cert=read('prism-two-pair-failure.certificate.json')
        cert['overlap_witness']['edge_witnesses'].pop()
        with self.assertRaisesRegex(ValueError,'Missing edge witnesses'):verify_overlap(cert)

    def test_thesis_chart_correspondence_and_exact_failure(self):
        cert=read('thesis-chart-DF.certificate.json');labels=cert['thesis_vertex_labels']
        mapped=[set(labels[v] for v in f) for f in cert['faces']]
        expected=[{1,2,3},{1,2,4},{2,3,5},{1,3,6},{2,4,5},{3,5,6},{1,4,6},{4,5,6}]
        self.assertEqual(mapped,expected)
        cuts={tuple(sorted(labels[v] for v in e)) for e in cert['cut_edges']}
        self.assertEqual(cuts,{(1,4),(2,5),(3,6),(4,6),(5,6)})
        self.assertEqual(verify_overlap(cert)['faces'],[4,6])

    def test_polygon_checker_accepts_known_octahedron_point(self):
        old=read('octahedron-box.certificate.json')
        p=[[str((F(q[0])+F(q[1]))/2) for q in pt] for pt in old['coordinate_box']]
        cert=make_certificate(point_spec(p,old['faces'],old['cut_edges']))
        self.assertEqual(sum(verify(cert)['pairs'].values()),28)


if __name__=='__main__':unittest.main()
