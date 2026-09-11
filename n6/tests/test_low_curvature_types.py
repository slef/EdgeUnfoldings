import json
from pathlib import Path
import unittest
from n6.families import MINUS_FACES,PRISM_FACES
from n6.intervals import set_precision
from n6.low_curvature_types import candidate_trees,verify
from n6.low_curvature_examples import specification
from n6.polycert import Geometry,make_certificate,verify as all_pairs
from n6.prism_paths import polygon_angle_product
from n6.regimes import curvature_pi


class LowCurvatureTypesTests(unittest.TestCase):
    def setUp(self):set_precision(240)

    def test_original_candidates_and_missing_diagonals(self):
        for faces,count,diagonals in [(MINUS_FACES,4,[[2,3]]),(PRISM_FACES,6,[[0,5],[2,4]])]:
            family=candidate_trees(faces)
            self.assertEqual(len(family['candidate_trees']),count)
            self.assertEqual(family['artificial_diagonals'],diagonals)
            for t in family['candidate_trees']:
                self.assertFalse(set(map(tuple,t['cuts']))&set(map(tuple,diagonals)))

    def test_points_and_full_coordinate_regions(self):
        for name in ['minus','prism']:
            for region in [False,True]:
                with self.subTest(name=name,region=region):
                    cert=make_certificate(specification(name,region));report=verify(cert)
                    self.assertTrue(report['at_least_one_candidate_unfolds_by_written_theorem'])
                    self.assertFalse(report['input_tree_nonoverlap_checked'])
                    self.assertFalse(report['full_n6_proved'])
                    self.assertEqual(all_pairs(cert)['result'],'verified')

    def test_strict_boundary_not_silently_included(self):
        # An invertible affine image of the prism example has three 60-degree
        # angles at vertex 0, hence curvature exactly pi. Interval cancellation
        # may leave the phase unresolved; neither equality nor uncertainty is <.
        from n6.polycert import point_spec
        points=[[0,0,0],[5,5,0],[5,0,5],[0,5,5],[6,10,6],[6,5,11]]
        faces=[list(reversed(f)) for f in PRISM_FACES]
        cuts=candidate_trees(faces)['candidate_trees'][0]['cuts']
        spec=point_spec(points,faces,cuts);g=Geometry(spec)
        self.assertNotEqual(curvature_pi(polygon_angle_product(g,0)),'<')
        with self.assertRaisesRegex(ValueError,'strictly below pi'):verify(spec)

    def test_constructed_refinements_keep_diagonals_uncut(self):
        from fractions import Fraction as F
        from n6.intervals import cross,sub
        from n6.point_audit import exact_hull
        from n6.polycert import point_spec
        from n6.source_choice import verify as source_check
        for name,moves in [('minus',[(2,0)]),('prism',[(0,1),(4,3)])]:
            spec=specification(name);family=candidate_trees(spec['faces'])
            points=[[F(q[0][0]) for q in point] for point in spec['coordinate_polynomials']]
            for epsilon in [F(1,10000),F(1,100000)]:
                p=[row[:] for row in points]
                for vertex,fi in moves:
                    a,b,c=spec['faces'][fi][:3]
                    normal=cross(sub(points[b],points[a]),sub(points[c],points[a]))
                    p[vertex]=[x+epsilon*n for x,n in zip(p[vertex],normal)]
                faces,adj=exact_hull(p)
                full={tuple(sorted((v,x))) for v,ns in adj.items() for x in ns}
                self.assertEqual(full-set(map(tuple,family['original_edges'])),set(map(tuple,family['artificial_diagonals'])))
                success=False
                for candidate in family['candidate_trees']:
                    v,w,c=(candidate[k] for k in ('source','fan','slit'));nxt={}
                    for f in faces:
                        if w in f:
                            j=f.index(w);nxt[f[(j+1)%3]]=f[(j+2)%3]
                    ring=[c]
                    while len(ring)<4:ring.append(nxt[ring[-1]])
                    refined={**point_spec(p,faces,candidate['cuts']),
                             'selection':dict(apex=v,antipode=w,equator=ring,slit_index=0)}
                    try:source_check(refined)
                    except ValueError:continue
                    self.assertEqual(all_pairs(make_certificate(refined))['result'],'verified')
                    success=True;break
                self.assertTrue(success,(name,epsilon))

    def test_high_curvature_counterexample_is_rejected(self):
        spec=json.loads((Path(__file__).parents[1]/'results/prism-two-pair-failure.certificate.json').read_text())
        with self.assertRaisesRegex(ValueError,'strictly below pi'):verify(spec)

    def test_wrong_type_rejected(self):
        from n6.selected_octahedron_examples import specification as octa_spec
        with self.assertRaises(ValueError):verify(octa_spec('regular-ties'))


if __name__=='__main__':unittest.main()
