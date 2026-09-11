import copy
import json
import unittest
from pathlib import Path

from n6.certify import tree_path
from n6.cut_rays import clip_entry, make_certificate, verify
from n6.far_pair_examples import source
from n6.intervals import I, det, sub, set_precision
from n6.polycert import Geometry


def points(rows):
    return [tuple(I(x) for x in row) for row in rows]


class CutRayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        set_precision(240)

    def test_finite_segment_safe_but_ray_enters(self):
        triangle = points([(2,-1), (4,-1), (3,1)])
        origin, endpoint = points([(0,0), (1,0)])
        self.assertTrue(clip_entry(triangle, origin, endpoint)['interior_entry_excluded'])
        self.assertFalse(clip_entry(triangle, origin, endpoint, False)['interior_entry_excluded'])

    def test_segment_through_petal_is_not_certified(self):
        triangle = points([(2,-1), (4,-1), (3,1)])
        origin, endpoint = points([(0,0), (5,0)])
        self.assertFalse(clip_entry(triangle, origin, endpoint)['interior_entry_excluded'])

    def test_ray_touching_vertex_is_allowed(self):
        triangle = points([(2,0), (3,1), (1,1)])
        origin, endpoint = points([(0,0), (4,0)])
        self.assertTrue(clip_entry(triangle, origin, endpoint, False)['interior_entry_excluded'])

    def test_widened_bounds_cannot_inherit_point_clearance(self):
        triangle = points([(2,-1), (4,-1), (3,1)])
        origin = points([(0,0)])[0]
        endpoint = (I(1,5), I(0))
        self.assertFalse(clip_entry(triangle, origin, endpoint)['interior_entry_excluded'])

    def test_clockwise_triangle_rejected(self):
        triangle = points([(2,-1), (3,1), (4,-1)])
        origin, endpoint = points([(0,0), (1,0)])
        with self.assertRaisesRegex(ValueError, 'orientation'):
            clip_entry(triangle, origin, endpoint)

    def test_existing_past_X_region_passes_two_segment_checks(self):
        cert = make_certificate(source('apex-entry-family'))
        self.assertNotIn('pair_witnesses', cert)
        self.assertNotIn('far_pair_witnesses', cert)
        report = verify(cert)
        self.assertEqual(report['parameter_dimension'], 11)
        self.assertTrue(report['whole_selected_net_nonoverlapping'])
        self.assertTrue(report['both_infinite_rays_also_clear'])
        self.assertTrue(report['direction_only_corollary_applies'])
        self.assertFalse(report['universal_lemma_F_proved'])

    def test_selection_requires_matching_cut_tree(self):
        cert = copy.deepcopy(source('apex-entry'))
        cert['selection']['slit_index'] = 1
        with self.assertRaisesRegex(ValueError, 'Cuts disagree'):
            verify(cert)

    def test_other_slit_requires_its_own_ranking(self):
        cert = copy.deepcopy(source('apex-entry'))
        s = cert['selection']; s['slit_index'] = 1
        cert['cut_edges'] = [[s['apex'],u] for u in s['equator']]+[[s['antipode'],s['equator'][1]]]
        with self.assertRaisesRegex(ValueError, 'Curvature comparison'):
            verify(cert)

    def test_real_hinge_counterexample_enters_finite_cut(self):
        root = Path(__file__).resolve().parents[1]
        spec = json.loads((root/'results/hinge-boundary-counterexample.certificate.json').read_text())
        g = Geometry(spec)
        claim = spec['hinge_audit']
        v, w, u = (claim[k] for k in ('source', 'sector_vertex', 'slit_vertex'))
        pair = spec['overlap_witness']['faces']
        fan_id = next(f for f in pair if w in g.faces[f])
        petal_id = next(f for f in pair if v in g.faces[f])
        fan = g.develop((fan_id,))
        petal = g.develop(tree_path(g.adj, fan_id, petal_id))
        triangle = [petal[x] for x in g.faces[petal_id]]
        self.assertFalse(clip_entry(triangle, fan[w], fan[u])['interior_entry_excluded'])
        t = I(claim['cut_crossing_fraction'])
        point = tuple((1-t)*a+t*b for a,b in zip(fan[w],fan[u]))
        self.assertTrue(all(det(sub(b,a),sub(point,a)).lo>0
                            for a,b in zip(triangle,triangle[1:]+triangle[:1])))
        spec['selection'] = dict(apex=0, antipode=1, equator=[2,3,4,5], slit_index=0)
        with self.assertRaisesRegex(ValueError, 'Curvature comparison'):
            verify(spec)


if __name__ == '__main__':
    unittest.main()
