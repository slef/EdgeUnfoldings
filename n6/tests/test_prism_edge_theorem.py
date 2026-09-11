import json
from pathlib import Path
import unittest
from n6.intervals import set_precision
from n6.prism_angle_identities import verify as angle_identities,expressions
from n6.prism_one_pair import verify as one_pair
from n6.prism_edge_theorem import select,candidates
from n6.prism_two_sharp_ends import specification
from n6.polycert import verify as all_pairs,verify_overlap
from n6.trees import tree_data
from n6.families import PRISM_FACES

ROOT=Path(__file__).resolve().parents[1]/'results'


class CompletePrismTests(unittest.TestCase):
    def setUp(self):set_precision(240)

    def test_three_angle_identities_vanish_as_exact_polynomials(self):
        r=angle_identities()
        self.assertEqual(r['independent_angle_indeterminates'],14)
        self.assertTrue(all(p.is_zero() for p in expressions()))
        self.assertFalse(r['geometry_or_positivity_formally_verified'])

    def test_all_seven_candidates_are_distinct_original_spanning_trees(self):
        options=candidates();self.assertEqual(len(options),7)
        self.assertEqual(len({tuple(map(tuple,t['cut_edges'])) for t in options}),7)
        original={tuple(sorted((f[i],f[(i+1)%len(f)]))) for f in PRISM_FACES for i in range(len(f))}
        for t in options:
            self.assertTrue(set(map(tuple,t['cut_edges']))<=original)
            tree_data(PRISM_FACES,t['cut_edges'])

    def test_one_pair_reduction_does_not_claim_a_failed_net_is_safe(self):
        for name in ['prism-two-pair-failure','prism-one-sharp-failure']:
            s=json.loads((ROOT/(name+'.certificate.json')).read_text());r=one_pair(s)
            self.assertEqual(r['pairs_proved'],14);self.assertEqual(r['remaining_pairs'],[[1,3]])
            self.assertFalse(r['whole_net_claimed'])
            self.assertEqual(verify_overlap(s)['result'],'verified_positive_area_overlap')

    def test_seven_tree_rule_repairs_old_failures_and_covers_exact_boundaries(self):
        specs=[json.loads((ROOT/(name+'.certificate.json')).read_text()) for name in ['prism-two-pair-failure','prism-one-sharp-failure','original-rule-prism-selected-failure','flat-hinges-prism-boundary']]
        specs.append(specification('both_boundaries'))
        for s in specs:
            r=select(s)
            self.assertEqual(all_pairs(r['certificate'])['result'],'verified')
            self.assertNotIn('overlap_witness',r['certificate'])
            self.assertIn(r['cut_edges'],[t['cut_edges'] for t in candidates()])

    def test_full_new_chart_is_one_domain_not_a_list_of_samples(self):
        s=json.loads((ROOT/'prism-complementary-family.certificate.json').read_text())
        r=select(s)
        self.assertEqual(r['independent_all_original_pairs']['parameter_dimension'],9)
        self.assertEqual(all_pairs(r['certificate'])['result'],'verified')


if __name__=='__main__':unittest.main()
