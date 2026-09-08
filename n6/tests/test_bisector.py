from copy import deepcopy
import json
from pathlib import Path
import unittest
from n6.bisector import verify as verify_bisector
from n6.polycert import verify as verify_net


class BisectorWitnessTests(unittest.TestCase):
    def test_failed_separator_is_compatible_with_a_simple_net(self):
        path = Path(__file__).resolve().parents[1]/'results/local-bisector-failure.certificate.json'
        cert = json.loads(path.read_text())
        self.assertEqual(verify_bisector(cert)['result'], 'verified_failure_of_bisector_separator')
        self.assertEqual(verify_net(cert)['result'], 'verified')
        bad = deepcopy(cert); bad['bisector_failure']['petal'] = 'first'
        with self.assertRaisesRegex(ValueError, 'failure not certified'):
            verify_bisector(bad)


if __name__ == '__main__':
    unittest.main()
