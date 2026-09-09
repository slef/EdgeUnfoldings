import json
from itertools import product
from pathlib import Path
import unittest
import numpy as np
from n6.octa_patterns import FACES, canonical_points, four_slit_obligations, selection_rules, failure_case_analysis
from n6.minus_patterns import TreeBatch
from n6.original_star_probe import apex_curvature
from n6.prism_diagonal import develop, pair_score
from n6.sector_probe import two_face_paths, sector_choices
from n6.trees import degree_four_stars


class OctaPatternTests(unittest.TestCase):
    def test_all_384_batch_developments_match_independent_implementation(self):
        batch = TreeBatch(faces=FACES)
        self.assertEqual(len(batch.trees), 384)
        fixtures = [np.array([[0,0,1],[0,0,-1],[1,0,0],[0,1,0],[-1,0,0],[0,-1,0]]),
                    np.array([[-100,0,-3],[62,14,-1],[57,-22,0],[-80,-1,2],[-8,4,4],[69,5,-1]])]
        for raw in fixtures:
            p = canonical_points(raw)
            self.assertIsNotNone(p)
            net = batch.nets(p)
            margins = batch.margins(p)
            for i, tree in enumerate(batch.trees):
                expected = develop(p, FACES, tree['hinges'], root=0)
                for f in range(8):
                    np.testing.assert_allclose(net[i,f], expected[f], atol=1e-11)
                reference = min(-pair_score(expected[a], expected[b]) for a,b in tree['pairs'])
                self.assertAlmostEqual(margins[i], reference, places=10)

    def test_four_slit_reduction_against_independent_product_enumeration(self):
        report = four_slit_obligations()
        self.assertEqual(report['distinct_placements'], 24)
        by_slit = [[e['id'] for e in report['events'] if slit in e['bad_slits']] for slit in range(2,6)]
        self.assertEqual(list(map(len, by_slit)), [9]*4)
        # Choose a failing pair separately in each net (9**4 possibilities),
        # then discard every event set containing an already sufficient set.
        candidates = {frozenset(c) for c in product(*by_slit)}
        minimal = []
        for c in sorted(candidates, key=lambda s: (len(s), sorted(s))):
            if not any(t <= c for t in minimal):
                minimal.append(c)
        self.assertEqual(len(minimal), 315)
        self.assertEqual(report['minimal_covers'], len(minimal))
        self.assertEqual(report['symmetry_classes'], 49)
        self.assertEqual(sum(c['size'] for c in report['classes']), len(minimal))
        for c in report['classes']:
            self.assertIn(frozenset(c['representative']), minimal)

    def test_regular_octahedron_shortest_paths_and_sector_choices(self):
        p = np.array([[0,0,1],[0,0,-1],[1,0,0],[0,-1,0],[-1,0,0],[0,1,0]], dtype=float)
        paths = two_face_paths(p, FACES, 0, 1)
        self.assertEqual(len(paths), 4)
        np.testing.assert_allclose([t[0] for t in paths], np.sqrt(6))
        trees = degree_four_stars(FACES)
        plans = [(t['apex'], t['antipode'], t['slit_vertex'], None) for t in trees]
        curvature = np.array([apex_curvature(p, FACES, v) for v in range(6)])
        choices = sector_choices(p, FACES, plans, 2*np.pi-curvature)
        self.assertEqual(len(choices), 12)
        self.assertEqual(len(selection_rules(p, trees, curvature)['sharpest_apex_geodesic_endpoints']), 2)

    def test_local_repair_and_reduced_failure_classes(self):
        report = failure_case_analysis()
        self.assertEqual(len(report['local_pair_repairs']), 12)
        for repair in report['local_pair_repairs']:
            self.assertEqual(len(repair['alternatives']), 3)
            self.assertEqual({a['slit_vertex'] for a in repair['alternatives']}, set(range(2,6))-{repair['old_slit']})
            for alternative in repair['alternatives']:
                self.assertTrue(all(repair['old_slit'] in FACES[f] for f in alternative['hinge_path']))
        reduced = report['reduced']
        self.assertEqual((reduced['raw_pair_checks'], reduced['distinct_placements']), (20,16))
        by_slit = [[e['id'] for e in reduced['events'] if k in e['bad_slits']] for k in range(2,6)]
        self.assertEqual(list(map(len, by_slit)), [5]*4)
        minimal = []
        for c in sorted({frozenset(c) for c in product(*by_slit)}, key=lambda s: (len(s), sorted(s))):
            if not any(t <= c for t in minimal):
                minimal.append(c)
        self.assertEqual(len(minimal), 131)
        self.assertEqual(sum(c['size'] for c in reduced['classes']), 131)
        self.assertEqual((reduced['symmetry_classes'], report['geometric_classes_excluded'], report['remaining_classes']), (24,1,23))
        excluded = [c for c in reduced['classes'] if c['status'] != 'open']
        self.assertEqual([c['original_class_id'] for c in excluded], [49])

    def test_angle_identity_and_existence_of_adjacent_large_sums(self):
        report = failure_case_analysis()
        for identity in report['opposite_route_identities']:
            self.assertEqual(set(map(tuple, identity['base_angle_terms'])), {(i,s) for i in range(4) for s in ('left','right')})
            self.assertEqual(len(identity['base_angle_terms']), 8)
        # Each opposite pair of sums has total > 2*pi, so it cannot contain
        # two small sums. Every such Boolean pattern has adjacent large sums.
        for large in product((False,True), repeat=4):
            if not (large[0] or large[2]) or not (large[1] or large[3]):
                continue
            self.assertTrue(any(large[k] and large[(k+1)%4] for k in range(4)))

    def test_exact_radial_obstruction_is_not_lost_by_numeric_sector_probe(self):
        filename = Path(__file__).resolve().parents[1]/'results/sector-sharpest-radial-failure.certificate.json'
        cert = json.loads(filename.read_text())
        p = np.array([[sum(float(c) for c, powers in q) for q in v] for v in cert['coordinate_polynomials']])
        faces = cert['faces']
        trees = degree_four_stars(faces)
        plans = [(t['apex'], t['antipode'], t['slit_vertex'], None) for t in trees]
        curvature = np.array([apex_curvature(p, faces, v) for v in range(6)])
        choices = sector_choices(p, faces, plans, 2*np.pi-curvature)
        sharp = cert['radial_obstruction']['sector_vertex']
        self.assertEqual(int(np.argmax(curvature)), sharp)
        self.assertFalse(any(w == sharp for v,w,u in choices))
        self.assertTrue(choices, 'The obstruction only defeats the fixed-sector-vertex strategy')


if __name__ == '__main__':
    unittest.main()
