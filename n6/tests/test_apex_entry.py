import copy
import json
from pathlib import Path
import unittest
from n6.apex_entry import verify
from n6.polycert import verify as verify_net

class ApexEntryTests(unittest.TestCase):
    def test_apex_can_enter_while_the_whole_net_is_simple(self):
        cert=json.loads((Path(__file__).resolve().parents[1]/'results/caseB-apex-entry.certificate.json').read_text())
        result=verify(cert)
        self.assertEqual(result['angle_comparison'],'Sigma_W+a < pi')
        self.assertTrue(result['left_apex_strictly_inside_outer_wedge'])
        self.assertTrue(result['right_petal_strictly_outside_outer_wedge'])
        self.assertEqual(verify_net(cert)['result'],'verified')

    def test_wrong_triple_and_wrong_side_are_rejected(self):
        cert=json.loads((Path(__file__).resolve().parents[1]/'results/caseB-apex-entry.certificate.json').read_text())
        bad=copy.deepcopy(cert);bad['apex_entry']['triple_index']=3
        with self.assertRaisesRegex(ValueError,'crosses the slit'):verify(bad)
        bad=copy.deepcopy(cert);bad['apex_entry']['side']='right'
        with self.assertRaisesRegex(ValueError,'left-apex'):verify(bad)

    def test_full_eleven_parameter_neighborhood(self):
        from fractions import Fraction as F
        cert=json.loads((Path(__file__).resolve().parents[1]/'results/caseB-apex-entry-region.certificate.json').read_text())
        self.assertEqual(len(cert['parameter_box']),11)
        self.assertTrue(all(F(b)-F(a)==F(1,500) for a,b in cert['parameter_box']))
        result=verify(cert)
        self.assertTrue(result['left_apex_strictly_inside_outer_wedge'])
        self.assertTrue(result['left_far_vertex_strictly_past_X'])
        self.assertTrue(result['right_petal_strictly_outside_outer_wedge'])
        self.assertEqual(verify_net(cert)['pairs'],{'vertex_fan':19,'separating_edge':9})

if __name__=='__main__':unittest.main()
