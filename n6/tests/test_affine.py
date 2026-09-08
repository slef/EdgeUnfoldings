from fractions import Fraction as F
import itertools
import json
from pathlib import Path
import unittest
from n6.affine import A
from n6.intervals import I
from n6.polycert import make_certificate,verify


class AffineArithmeticTests(unittest.TestCase):
    def test_shared_linear_terms_cancel(self):
        x=A.variable(-1,1,0)
        self.assertEqual((x-x).pair(),['0','0'])
        self.assertEqual((3*x-2*x-x).pair(),['0','0'])
        self.assertEqual((I(3)+x-x).pair(),['3','3'])

    def test_rational_products_and_division_enclose_correlated_values(self):
        x=A.variable('2/3','4/3',0);y=A.variable('-1/5','1/7',1)
        expressions=[(x+y)*(x-y),x/(2+x+y),(x-y).square(),1/(x-3),I(2)/(3+x),I(1)-x]
        for a,b in itertools.product([F(2,3),F(5,6),F(1),F(4,3)],[F(-1,5),F(0),F(1,7)]):
            values=[(a+b)*(a-b),a/(2+a+b),(a-b)**2,1/(a-3),2/(3+a),1-a]
            for expr,value in zip(expressions,values):
                self.assertLessEqual(expr.lo,value);self.assertGreaterEqual(expr.hi,value)

    def test_square_roots_against_higher_precision_point_intervals(self):
        import n6.intervals as arithmetic
        x=A.variable('1/3','2/3',0);y=A.variable('-1/8','1/8',1)
        result=((x-y).square()+2*x+1).sqrt()/(x+2)
        old=arithmetic.SCALE
        try:
            arithmetic.SCALE=1<<320
            for a,b in itertools.product([F(1,3),F(1,2),F(2,3)],[F(-1,8),F(0),F(1,8)]):
                value=I((a-b)**2+2*a+1).sqrt()/(a+2)
                self.assertLessEqual(result.lo,value.lo);self.assertGreaterEqual(result.hi,value.hi)
        finally:arithmetic.SCALE=old

    def test_square_nonnegativity_and_zero_boundary(self):
        x=A.variable('-1','2',0)
        self.assertGreaterEqual(x.square().lo,0)
        y=x.square().sqrt()
        self.assertLessEqual(y.lo,0);self.assertGreaterEqual(y.hi,2)
        self.assertEqual(A(0).sqrt().pair(),['0','0'])

    def test_undefined_operations_and_floats_are_rejected(self):
        with self.assertRaises(TypeError):A(.1)
        with self.assertRaises(ValueError):1/A.variable(-1,1,0)
        with self.assertRaises(ValueError):A.variable(-1,1,0).sqrt()

    def test_existing_nine_parameter_geometry_with_affine_bounds(self):
        path=Path(__file__).resolve().parents[1]/'results/prism-region.certificate.json'
        spec=json.loads(path.read_text());spec['arithmetic_mode']='affine'
        report=verify(make_certificate(spec))
        self.assertTrue(report['linear_correlations'])
        self.assertEqual(sum(report['pairs'].values()),15)


if __name__=='__main__':unittest.main()
