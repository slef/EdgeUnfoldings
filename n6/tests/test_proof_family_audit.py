import json
from pathlib import Path
import unittest
from n6.proof_family_audit import verify as audit
from n6.polycert import verify
from n6.intervals import set_precision


class ProofFamilyAuditTests(unittest.TestCase):
    def setUp(self):
        set_precision(240);self.root=Path(__file__).resolve().parents[1]/'results'

    def test_exact_uncovered_example_still_unfolds(self):
        c=json.loads((self.root/'octa-new-criteria-uncovered.certificate.json').read_text())
        report=audit(c)
        self.assertEqual(report['result'],'verified_outside_three_new_simple_criteria')
        self.assertEqual(len(report['vertices']),6)
        self.assertEqual(len(report['sharpest_patch_classification']['nonconvex_patches']),2)
        self.assertEqual(verify(c)['result'],'verified')

    def test_covered_examples_cannot_be_reported_uncovered(self):
        for name in ('zero','one','two-opposite'):
            c=json.loads((self.root/('octa-patches-'+name+'.certificate.json')).read_text())
            with self.assertRaises(ValueError):audit(c)


if __name__=='__main__':unittest.main()
