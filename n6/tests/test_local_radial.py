import json
from pathlib import Path
import unittest
from n6.local_radial import verify,verify_clearance
from n6.polycert import verify as verify_net


class LocalRadialTests(unittest.TestCase):
    def test_angular_overlap_and_simple_net_are_both_exact(self):
        path=Path(__file__).resolve().parents[1]/'results/local-radial-failure.certificate.json'
        cert=json.loads(path.read_text())
        self.assertEqual(verify(cert)['result'],'verified_failure_of_local_radial_separator')
        self.assertEqual(verify_net(cert)['result'],'verified')

    def test_shared_rays_have_a_positive_distance_gap(self):
        path=Path(__file__).resolve().parents[1]/'results/local-radial-failure.certificate.json'
        cert=json.loads(path.read_text())
        result=verify_clearance(cert)
        self.assertEqual(result['minimum_distance_ratio'],'1217/1000')
        cert['local_radial_clearance']['minimum_distance_ratio']='5/4'
        with self.assertRaisesRegex(ValueError,'clearance'):verify_clearance(cert)

    def test_wrong_flank_is_not_accepted(self):
        path=Path(__file__).resolve().parents[1]/'results/local-radial-failure.certificate.json'
        cert=json.loads(path.read_text());cert['local_radial_failure']['petal']='last'
        with self.assertRaisesRegex(ValueError,'apex ray'):verify(cert)


if __name__=='__main__':unittest.main()
