import json
from pathlib import Path
import unittest
import numpy as np
from n6.minus_pair import paired_trees,obligations,verify_bundle,select_certificate
from n6.minus_patterns import TreeBatch,canonical_points,valid_points
from n6.families import MINUS_FACES as FACES
from n6.prism_diagonal import develop,pair_score
from n6.polycert import verify
from n6.cover import read_cover,leaves,summary

RESULTS=Path(__file__).resolve().parents[1]/'results'
def read(name):return json.loads((RESULTS/name).read_text())


class MinusPairTests(unittest.TestCase):
    def test_batch_matches_original_development_for_every_tree(self):
        batch=TreeBatch()
        fixtures=[[[0,0,0],[10,0,0],[18,-5,0],[-27,10,0],[22,-5,-1],[-62,24,-5]],
                  [[0,0,0],[10,0,0],[16,-3,0],[-42,13,0],[-58,0,-6],[-133,9,-10]]]
        for raw in fixtures:
            p=valid_points(raw);net=batch.nets(p);margins=batch.margins(p)
            for i,t in enumerate(batch.trees):
                expected=develop(p,FACES,t['hinges'],root=0)
                for f,face in enumerate(FACES):np.testing.assert_allclose(net[i,f,:len(face)],expected[f],atol=1e-11)
                expected_margin=min(-pair_score(expected[a],expected[b]) for a,b in t['pairs'])
                self.assertAlmostEqual(margins[i],expected_margin,places=10)
            transformed=canonical_points(p)
            normalized=valid_points(transformed)
            np.testing.assert_allclose(batch.margins(normalized),margins,atol=1e-10)

    def test_complete_four_route_failure_is_exact(self):
        report=verify_bundle(read('minus-quad-paths.certificate.json'))
        self.assertEqual(report['result'],'verified_family_failure')
        self.assertEqual(report['verified_failures'],4)

    def test_both_directions_require_a_choice(self):
        for stem,apex in [('minus-pair-switch',5),('minus-pair-switch-reflected',4)]:
            bundle=read(stem+'.certificate.json');report=verify_bundle(bundle)
            self.assertEqual((report['verified_failures'],report['verified_successes']),(1,1))
            selected=select_certificate(bundle['cases'][0]['certificate'])
            self.assertEqual(selected['selected_apex'],apex)
            self.assertNotIn('overlap_witness',selected['certificate'])
            self.assertEqual(verify(selected['certificate'])['result'],'verified')

    def test_audit_rejects_missing_tree_or_different_geometry(self):
        bundle=read('minus-quad-paths.certificate.json');bundle['cases'].pop()
        with self.assertRaisesRegex(ValueError,'omits trees'):verify_bundle(bundle)
        bundle=read('minus-pair-switch.certificate.json')
        bundle['cases'][1]['certificate']['coordinate_polynomials'][1][0][0][0]='11'
        with self.assertRaisesRegex(ValueError,'different shapes'):verify_bundle(bundle)

    def test_all_failure_combinations_are_partitioned_by_symmetry(self):
        report=obligations()
        self.assertEqual(report['symmetry_classes'],28)
        self.assertEqual(sum(len(orbit) for orbit in report['orbits']),49)
        self.assertEqual(sum(len(orbit)==1 for orbit in report['orbits']),7)

    def test_new_cover_has_same_root_and_only_one_prescribed_tree(self):
        old=read_cover(RESULTS/'minus-merged-cover.certificate.json.gz')
        new=read_cover(RESULTS/'minus-pair-cover.certificate.json.gz')
        self.assertEqual(old['geometry'],new['geometry'])
        self.assertEqual(summary(new)['parameter_volume_fractions'],{'certified':'1'})
        cells=list(leaves(new));self.assertEqual(len(cells),16)
        self.assertEqual({tuple(map(tuple,node['cuts'])) for node,_,_ in cells},{tuple(paired_trees()[0]['cuts'])})


if __name__=='__main__':unittest.main()
