import copy,json,unittest
from n7.bipyramid_star_patch import ROOT,certify,certify_failure,replay_saved
from n7.bipyramid_receiver_pairs import replay_saved as replay_pairs

class StarPatchChecks(unittest.TestCase):
    def rows(self):return json.loads((ROOT/'results/bipyramid-star-patch.json').read_text())
    def test_exact_successes_and_four_tree_failures(self):
        result=replay_saved();self.assertEqual(result['exact_successes'],6)
        self.assertEqual(result['four_tree_counterexamples'],2)
        for row in self.rows()['examples']:
            n=row['certificate']['independent_net_check']
            self.assertEqual(len(n['shared_vertex_pairs'])+len(n['strict_separators']),45)
        high=[r for r in self.rows()['examples'] if r['gate']=='large pole']
        self.assertIn(3,[5-r['certificate']['pattern'].count('C') for r in high])
        self.assertIn(4,[5-r['certificate']['pattern'].count('C') for r in high])
        self.assertTrue(any(r.get('require_acute_ring_corners') for r in high))
    def test_overlapping_candidate_cannot_pass_large_pole_gate(self):
        r=self.rows()['counterexamples'][0]
        r.update(fan_pole=5,slit=r['patch'],gate='large pole')
        with self.assertRaises(ValueError):certify(r)
    def test_missing_endpoint_failure_is_rejected(self):
        r=self.rows()['counterexamples'][0];r['choices'].pop()
        with self.assertRaises(ValueError):certify_failure(r)
    def test_false_overlap_witness_is_rejected(self):
        r=self.rows()['counterexamples'][0];r['choices'][0]['witness']=['999999','999999']
        with self.assertRaises(ValueError):certify_failure(r)
    def test_both_auxiliary_pole_edge_stars(self):
        replay_pairs()
        rows=json.loads((ROOT/'results/bipyramid-receiver-pairs.json').read_text())['examples']
        aux=next(r['certificate']['auxiliary_pole_edge'] for r in rows if r.get('auxiliary_pole_edge'))
        self.assertEqual(aux['deleted_vertex'],0)
        for net in aux['source_nets'].values():
            self.assertEqual(len(net['shared_vertex_pairs'])+len(net['strict_separators']),28)

if __name__=='__main__':unittest.main()
