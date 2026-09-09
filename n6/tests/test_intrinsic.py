import itertools
import json
from pathlib import Path
import unittest
import z3
from n6.intrinsic import sum_angles_lt_turn,checked_sum,metric_angles,verify,query
from n6.intervals import I


class IntrinsicMetricTests(unittest.TestCase):
    def test_query_accepts_a_shared_heronian_metric_before_target(self):
        # All eight triangles have side ratios 13:13:10 and altitude 12.
        # Their areas and all products are rational, with no expensive solver
        # or algebraic-number search in the regression test.
        for slit in (0,3):
            assertions,variables=query(slit_index=slit)
            bindings=[(v,z3.RealVal('100/169' if name=='l' else '1'))
                      for name,row in variables.items() for v in row]
            bindings += [(z3.Real(f'area4_{i}'),z3.RealVal('240/169')) for i in range(8)]
            evaluated=[z3.simplify(z3.substitute(a,*bindings)) for a in assertions]
            self.assertTrue(all(z3.is_true(a) for a in evaluated[:-1]))
            self.assertTrue(z3.is_false(evaluated[-1]))

    def test_full_turn_boundary_and_multiple_wraps(self):
        rays={1:(1,1),2:(0,1),3:(-1,1)}
        for n in range(1,7):
            for angles in itertools.product(rays,repeat=n):
                zs=[rays[a] for a in angles]
                self.assertEqual(z3.is_true(z3.simplify(sum_angles_lt_turn(zs))),sum(angles)<8,angles)
                if sum(angles)<8:checked_sum([tuple(I(x) for x in z) for z in zs])
                else:
                    with self.assertRaises(ValueError):checked_sum([tuple(I(x) for x in z) for z in zs])

    def test_invalid_triangle_is_rejected(self):
        q={n:['1']*4 for n in ('s','r','l')};q['l'][0]='9'
        with self.assertRaisesRegex(ValueError,'Triangle inequality'):metric_angles(q)

    def test_exact_metric_countermodel_requires_the_cone_omission(self):
        spec=json.loads((Path(__file__).resolve().parents[1]/'results/intrinsic-without-cone.certificate.json').read_text())
        report=verify(spec)
        self.assertEqual(report['result'],'verified_intrinsic_angle_countermodel')
        self.assertTrue(any(report['proved_cone_violations_by_vertex']))
        spec['require_cone']=True
        with self.assertRaisesRegex(ValueError,'cone inequality'):verify(spec)

    def test_invalid_slit_cannot_certify_a_different_net(self):
        spec=json.loads((Path(__file__).resolve().parents[1]/'results/intrinsic-without-cone.certificate.json').read_text())
        spec['slit_index']=1
        with self.assertRaisesRegex(ValueError,'crosses the slit'):verify(spec)


if __name__=='__main__':unittest.main()
