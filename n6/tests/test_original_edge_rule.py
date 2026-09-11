import json
from pathlib import Path
import unittest
from n6.flat_octahedron import verify_fixed_tree,original_candidates
from n6.intervals import I,set_precision
from n6.original_edge_examples import specification,verify_selected_failure
from n6.original_edge_rule import verify,small_fan_budget,sum_pi,ring_for
from n6.polycert import make_certificate,verify as all_pairs
from n6.families import MINUS_FACES,PRISM_FACES


class OriginalEdgeRuleTests(unittest.TestCase):
    def setUp(self):set_precision(240)

    def test_new_families_and_independent_original_pair_replay(self):
        for kind in ('minus','prism'):
            for region in (False,True):
                with self.subTest(kind=kind,region=region):
                    spec=specification(kind,region)
                    self.assertTrue(verify(spec)['whole_net_safe_by_written_theorem'])
                    self.assertEqual(all_pairs(make_certificate(spec))['result'],'verified')
                    with self.assertRaises(ValueError):verify_fixed_tree(spec)

    def test_sum_and_half_angle_comparisons_do_not_wrap(self):
        # Curvatures c=w=45 degrees, so each incident-angle phase is -45.
        totals={0:(I(-1),I(0)),1:(I(1),I(-1)),2:(I(1),I(-1))}
        bands={0:'=',1:'<',2:'<'}
        self.assertEqual(small_fan_budget(totals,bands,0,1,2),'=')
        totals[0]=(I(0),I(-1));bands[0]='<'  # Gamma_v/2 = 135 degrees.
        self.assertEqual(small_fan_budget(totals,bands,0,1,2),'<')
        totals[0]=(I(0),I(1));bands[0]='>'   # Gamma_v/2 = 45 degrees.
        self.assertEqual(small_fan_budget(totals,bands,0,1,2),'>')
        totals[1]=totals[2]=(I(-1),I(-1))    # Each curvature is 135 degrees.
        self.assertEqual(sum_pi(totals,bands,[1,2,1]),'>')
        bands[1]=None
        self.assertIsNone(sum_pi(totals,bands,[1,2]))

    def test_exact_failure_rankings_overlap_and_same_solid_repairs(self):
        root=Path(__file__).resolve().parents[1]/'results'
        for kind in ('minus','prism'):
            cert=json.loads((root/f'original-rule-{kind}-selected-failure.certificate.json').read_text())
            self.assertTrue(verify_selected_failure(cert)['rankings_strict'])
            with self.assertRaises(ValueError):verify(cert)
            changed=json.loads(json.dumps(cert));changed['original_rule_selection']['slit']=changed['original_rule_selection']['source']
            with self.assertRaises(ValueError):verify_selected_failure(changed)
            repair=json.loads((root/f'original-rule-{kind}-repair.certificate.json').read_text())
            self.assertEqual(repair['coordinate_polynomials'],cert['coordinate_polynomials'])
            self.assertEqual(all_pairs(repair)['result'],'verified')

    def test_all_candidate_rings_close_and_avoid_both_poles(self):
        for faces,count in ((MINUS_FACES,14),(PRISM_FACES,6)):
            family,trees=original_candidates(faces);self.assertEqual(len(trees),count)
            for t in trees:
                r=ring_for(family,t['source'],t['fan'],t['slit'])
                self.assertEqual(set(r),set(range(6))-{t['source'],t['fan']})
                self.assertEqual(r[0],t['slit'])


if __name__=='__main__':unittest.main()
