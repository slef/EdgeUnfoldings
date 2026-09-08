import unittest
import z3
from n6.direct_query import direct_net,interior_overlap,formulation


class DirectDevelopmentTests(unittest.TestCase):
    def test_two_distance_equations_and_side_select_unique_triangle(self):
        points=[(0,0,0),(3,0,0),(0,4,0),(0,0,4)]
        faces=[(0,1,2),(1,0,3)]
        q,areas,constraints=direct_net(points,faces,[(0,1)],normalized_root=True)
        solver=z3.SolverFor('QF_NRA');solver.add(*constraints)
        self.assertEqual(solver.check(),z3.sat)
        solver.push();solver.add(z3.Or(q[1][3][0]!=0,q[1][3][1]!=-4))
        self.assertEqual(solver.check(),z3.unsat);solver.pop()
        solver.add(interior_overlap(q,faces,0,1))
        self.assertEqual(solver.check(),z3.unsat)

    def test_unaligned_spatial_root_is_developed_isometrically(self):
        points=[(2,1,3),(2,4,3),(2,1,7),(6,1,3)]
        faces=[(0,1,2),(1,0,3)]
        q,areas,constraints=direct_net(points,faces,[(0,1)])
        solver=z3.SolverFor('QF_NRA');solver.add(*constraints)
        self.assertEqual(solver.check(),z3.sat)
        solver.add(z3.Or(q[0][1][0]!=3,q[0][2][0]!=0,q[0][2][1]!=4,
                         q[1][3][0]!=0,q[1][3][1]!=-4))
        self.assertEqual(solver.check(),z3.unsat)

    def test_focused_queries_build_without_a_large_D_restriction(self):
        for target in ('local_vv','local_vw','opposite','caseB_small_SW','left_apex','right_apex'):
            assertions,metadata=formulation(target,lifted=True)
            self.assertEqual(len(metadata['cuts']),5)
            self.assertGreater(metadata['auxiliary_variables'],0)
            self.assertTrue(all(z3.is_bool(a) for a in assertions))


if __name__=='__main__':unittest.main()
