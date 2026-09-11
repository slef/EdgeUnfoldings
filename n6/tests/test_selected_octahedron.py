import json
from pathlib import Path
import unittest

from n6.curvature import point_angle_signature
from n6.intervals import set_precision
from n6.polycert import Geometry,make_certificate,verify as verify_all_pairs
from n6.selected_octahedron import verify
from n6.selected_octahedron_examples import specification


class SelectedOctahedronTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        set_precision(240)

    def test_both_strict_curvature_branches_are_whole_net_theorems(self):
        for name,branch in [('high-curvature','high_curvature_pole_angle'),
                            ('obtuse','low_curvature_equal_lengths')]:
            r=verify(specification(name))
            self.assertEqual(r['proof_branch'],branch)
            self.assertTrue(r['whole_selected_net_nonoverlapping'])
            self.assertFalse(r['every_slit_lemma_F_proved'])
            self.assertFalse(r['full_n6_proved'])

    def test_exact_180_degree_boundary(self):
        spec=specification('curvature-equality')
        r=verify(spec)
        self.assertEqual(r['source_curvature_comparison_with_pi'],'=')
        self.assertEqual(r['proof_branch'],'equality_covered_by_both_proofs')
        self.assertEqual(sum(verify_all_pairs(make_certificate(spec))['pairs'].values()),28)

    def test_one_coordinate_box_crosses_the_boundary_without_a_gap(self):
        spec=specification('crossing-threshold')
        r=verify(spec)
        self.assertIsNone(r['source_curvature_comparison_with_pi'])
        self.assertEqual(r['parameter_dimension'],18)
        self.assertEqual(r['proof_branch'],'curvature_unresolved_but_both_branches_proved')
        self.assertEqual(sum(verify_all_pairs(make_certificate(spec))['pairs'].values()),28)
        # Two exact members on opposite sides establish that this is a
        # real crossing box, not merely an inconclusive angle calculation.
        bands=set()
        for displacement in ('1/10000','-1/10000'):
            point=specification('curvature-equality')
            for coordinate in point['coordinate_polynomials'][0]:
                coordinate[0][0]=displacement
            bands.add(verify(point)['source_curvature_comparison_with_pi'])
        self.assertEqual(bands,{'<','>'})

    def test_exact_source_and_slit_ties_are_accepted_without_rounding(self):
        spec=specification('regular-ties')
        r=verify(spec)
        self.assertTrue(all(c['reason']=='identical exact incident-angle multisets'
                            for c in r['curvature_order']['comparisons']))
        self.assertEqual(sum(verify_all_pairs(make_certificate(spec))['pairs'].values()),28)

    def test_unequal_curvatures_do_not_inherit_the_tie_shortcut(self):
        spec=specification('curvature-equality');g=Geometry(spec)
        self.assertNotEqual(point_angle_signature(g,0),point_angle_signature(g,1))
        spec['selection'].update(apex=1,antipode=0,equator=[2,5,4,3])
        spec['cut_edges']=[[1,x] for x in (2,3,4,5)]+[[0,2]]
        with self.assertRaisesRegex(ValueError,'Curvature comparison'):
            verify(spec)

    def test_nontrivial_intervals_cannot_be_claimed_as_exact_angle_ties(self):
        self.assertIsNone(point_angle_signature(Geometry(specification('crossing-threshold')),0))

    def test_wrong_slit_and_actual_H_failing_overlap_are_rejected(self):
        spec=specification('low-curvature')
        spec['selection']['slit_index']=1
        with self.assertRaisesRegex(ValueError,'Cuts disagree'):
            verify(spec)
        spec=specification('low-curvature')
        spec['selection']['slit_index']=1
        spec['cut_edges'][-1]=[5,3]
        with self.assertRaisesRegex(ValueError,'Curvature comparison'):
            verify(spec)
        root=Path(__file__).resolve().parents[1]
        spec=json.loads((root/'results/hinge-boundary-counterexample.certificate.json').read_text())
        spec['selection']=dict(apex=0,antipode=1,equator=[2,3,4,5],slit_index=0)
        with self.assertRaisesRegex(ValueError,'Curvature comparison'):
            verify(spec)


if __name__=='__main__':
    unittest.main()
