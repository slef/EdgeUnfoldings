import copy
import json
from pathlib import Path
import unittest
from n6.families import PRISM_FACES
from n6.polycert import verify,verify_overlap
from n6.prism_paths import verify_shorter_failure
from n6.trees import quadrilateral_path_stars

RESULTS=Path(__file__).resolve().parents[1]/'results'
def read(name):return json.loads((RESULTS/name).read_text())

class PrismPathTests(unittest.TestCase):
    def test_four_original_edge_paths_and_exact_switching_example(self):
        trees=quadrilateral_path_stars(PRISM_FACES)
        self.assertEqual([(t['apex'],t['slit_vertex']) for t in trees],[(1,2),(1,4),(3,0),(3,5)])
        coordinates=None
        for t in trees:
            self.assertEqual(len(t['pairs']),4)
            cert=read(f"prism-path-apex{t['apex']}-via{t['slit_vertex']}.certificate.json")
            self.assertEqual(sorted(map(tuple,cert['cut_edges'])),t['cuts'])
            if coordinates is None:coordinates=cert['coordinate_polynomials']
            self.assertEqual(cert['coordinate_polynomials'],coordinates)
            report=(verify_overlap if t['apex']==1 else verify)(cert)
            self.assertEqual(report['result'],'verified_positive_area_overlap' if t['apex']==1 else 'verified')

    def test_shorter_path_fails_at_strictly_sharper_apex(self):
        cert=read('prism-shorter-path-failure.certificate.json')
        report=verify_shorter_failure(cert)
        self.assertEqual((report['apex'],report['via'],report['strictly_sharper_than']),(3,5,1))
        good=read('prism-longer-path-success.certificate.json')
        self.assertEqual(cert['coordinate_polynomials'],good['coordinate_polynomials'])
        self.assertEqual(verify(good)['result'],'verified')

    def test_relabeling_path_cannot_reuse_overlap_witness(self):
        cert=read('prism-shorter-path-failure.certificate.json')
        bad=copy.deepcopy(cert);bad['path_selection']['via']=0
        with self.assertRaisesRegex(ValueError,'cuts do not match'):verify_shorter_failure(bad)
        bad=copy.deepcopy(cert);bad['path_selection']['apex']=1
        with self.assertRaises(ValueError):verify_shorter_failure(bad)

if __name__=='__main__':unittest.main()
