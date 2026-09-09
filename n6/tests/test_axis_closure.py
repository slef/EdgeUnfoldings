import copy
from fractions import Fraction as F
import json
from pathlib import Path
import unittest
import z3
from n6.axis_closure import centered_value,expressions,metric_data,propose_leaf,symbolic_conditions,verify
from n6.intrinsic import verify as verify_intrinsic
from n6.polynomials import Poly

RESULTS=Path(__file__).resolve().parents[1]/'results'

class AxisClosureTests(unittest.TestCase):
    def test_exact_metric_satisfies_all_local_checks_but_cannot_close(self):
        cert=json.loads((RESULTS/'intrinsic-axis-nonclosure.certificate.json').read_text())
        local=verify_intrinsic(cert['metric'])
        self.assertTrue(all(local['strict_cone_inequalities_by_vertex']))
        self.assertTrue(local['strict_H_and_R'])
        report=verify(cert)
        self.assertEqual(report['closed_intervals'],5)
        self.assertEqual(report['checks'],{'tetrahedron_square_nonpositive':4,'closure_imag_positive':1})

    def test_regular_octahedron_is_not_excluded(self):
        lengths={n:['1']*4 for n in ('s','r','l')}
        polys,domain=metric_data({'squared_edge_lengths':lengths})
        self.assertLess(domain[0],2);self.assertGreater(domain[1],2)
        self.assertIsNone(propose_leaf(polys,(F(2),F(2))))
        assertions=symbolic_conditions({n:[z3.RealVal(x) for x in row] for n,row in lengths.items()})
        bindings=[(z3.Real('axis_squared'),z3.RealVal(2))]+[(z3.Real(f'axis_turn_area_{i}'),z3.RealVal(4)) for i in range(4)]
        self.assertTrue(all(z3.is_true(z3.simplify(z3.substitute(a,*bindings))) for a in assertions))
        wrong=[(z3.Real('axis_squared'),z3.RealVal(2))]+[(z3.Real(f'axis_turn_area_{i}'),z3.RealVal(-4)) for i in range(4)]
        self.assertFalse(all(z3.is_true(z3.simplify(z3.substitute(a,*wrong))) for a in assertions))

    def test_asymmetric_integer_octahedron_closes_exactly(self):
        P=[(0,0,0),(0,0,100),(81,0,65),(-8,6,112),(-10,0,37),(9,-4,86)]
        distance=lambda a,b:sum((x-y)**2 for x,y in zip(P[a],P[b]))
        lengths={'s':[distance(0,2+i) for i in range(4)],'r':[distance(1,2+i) for i in range(4)],
                 'l':[distance(2+i,2+(i+1)%4) for i in range(4)]}
        assertions=symbolic_conditions(lengths)
        heights=[40000*(P[2+i][0]*P[2+(i+1)%4][1]-P[2+i][1]*P[2+(i+1)%4][0]) for i in range(4)]
        bindings=[(z3.Real('axis_squared'),z3.RealVal(10000))]+[(z3.Real(f'axis_turn_area_{i}'),z3.RealVal(h)) for i,h in enumerate(heights)]
        self.assertTrue(all(z3.is_true(z3.simplify(z3.substitute(a,*bindings))) for a in assertions))

    def test_centered_polynomial_encloses_values(self):
        t=Poly.variable(1,0);p=t*t*t-57*t*t+1083*t-6859
        bound=centered_value(p,F(189,10),F(191,10)) # (t-19)^3
        self.assertEqual(bound.lo,-bound.hi)
        self.assertLessEqual(bound.lo,F(-1,1000));self.assertGreaterEqual(bound.hi,F(1,1000))

    def test_missing_domain_and_false_leaf_are_rejected(self):
        cert=json.loads((RESULTS/'intrinsic-axis-nonclosure.certificate.json').read_text())
        bad=copy.deepcopy(cert);bad['axis_squared_domain'][0]='19'
        with self.assertRaisesRegex(ValueError,'every possible'):verify(bad)
        bad=copy.deepcopy(cert);bad['tree']['left']['left']={'kind':'closure_imag_negative'}
        with self.assertRaises(ValueError):verify(bad)
        bad=copy.deepcopy(cert);bad['tree']['split']=bad['axis_squared_domain'][0]
        with self.assertRaisesRegex(ValueError,'subdivision'):verify(bad)

if __name__=='__main__':unittest.main()
