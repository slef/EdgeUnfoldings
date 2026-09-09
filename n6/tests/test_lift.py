import unittest
import z3
from n6.lift import arithmetic_lift, lifted_solver


class ArithmeticLiftTests(unittest.TestCase):
    def test_satisfiable_and_unsatisfiable_polynomial_formulas(self):
        x, y = z3.Reals('lift_test_x lift_test_y')
        p = (x*y + x + 3)**2 - x*y*(x-y)
        for original, expected in [
            ([x == 2, y == 1, p == 47], z3.sat),
            ([x == 2, y == 1, p != 47], z3.unsat),
            ([x > 0, y > 0, z3.Or(x*y < 0, p == p+1)], z3.unsat),
        ]:
            lifted, aux = arithmetic_lift(original)
            self.assertTrue(aux)
            solver = lifted_solver(5000); solver.add(*lifted)
            self.assertEqual(solver.check(), expected)
            if expected == z3.sat:
                self.assertTrue(all(z3.is_true(solver.model().eval(a)) for a in original))

    def test_invalid_fractional_power_is_not_silently_changed(self):
        x = z3.Real('lift_power_test')
        with self.assertRaisesRegex(ValueError, 'integer power'):
            arithmetic_lift([x**z3.RealVal('1/2') > 0])


if __name__ == '__main__':
    unittest.main()
