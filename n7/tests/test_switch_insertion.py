import json,unittest
from n7.bipyramid_switch_insertion import certify,replay_saved
from n7.bipyramid_morph import ROOT
class SwitchInsertionChecks(unittest.TestCase):
    def test_entire_schedule_and_minimum_vertex(self):
        self.assertEqual(replay_saved(),{'closed_interval_cells':128,'slit_changes':1,'inserted_vertex_minimum':True,'specified_net_checks':3})
        row=json.loads((ROOT/'results/bipyramid-switch-insertion.json').read_text());self.assertEqual(row['certificate']['target_pattern'],'FCFFC')
        for n in row['certificate']['independent_net_checks']:self.assertEqual(n['shared_vertex_pairs']+len(n['strict_separators']),45)
    def test_wrong_transition_bracket_rejected(self):
        row=json.loads((ROOT/'results/bipyramid-switch-insertion.json').read_text());row['switch_bracket']=['1/2','3/4']
        with self.assertRaisesRegex(ValueError,'does not straddle'):certify(row)
if __name__=='__main__':unittest.main()
