import copy,json
from pathlib import Path
import unittest
import numpy as np
from n6.hinge_audit import verify as audit
from n6.polycert import verify,Geometry
from n6.intervals import set_precision
from n6.minus_patterns import TreeBatch
from n6.octa_patterns import FACES
from n6.trees import degree_four_stars


class HingeAuditTests(unittest.TestCase):
    def setUp(self):
        set_precision(240);self.root=Path(__file__).resolve().parents[1]/'results'
        self.cert=json.loads((self.root/'hinge-boundary-counterexample.certificate.json').read_text())

    def test_real_overlap_with_all_other_pairs_clear(self):
        r=audit(self.cert)
        self.assertEqual(r['nonoverlapping_pairs'],27)
        self.assertEqual(r['overlap']['result'],'verified_positive_area_overlap')
        self.assertEqual(r['strictly_sharper_vertex'],4)

    def test_alternative_original_edge_unfolding(self):
        c=json.loads((self.root/'hinge-boundary-alternative.certificate.json').read_text())
        self.assertEqual(verify(c)['result'],'verified')

    def test_omitted_safe_pair_is_rejected(self):
        c=copy.deepcopy(self.cert);c['nonoverlap_witnesses'].pop()
        with self.assertRaisesRegex(ValueError,'Missing safe pairs'):audit(c)

    def test_json_tree_pairs_do_not_become_exempt(self):
        tree=next(t for t in degree_four_stars(FACES) if t['apex']==0 and t['slit_vertex']==2)
        restored=json.loads(json.dumps(tree));g=Geometry(self.cert)
        p=np.array([[(float(q.lo)+float(q.hi))/2 for q in row] for row in g.p])
        native=TreeBatch([tree],faces=FACES);loaded=TreeBatch([restored],faces=FACES)
        a,b=native.pair_scores(p),loaded.pair_scores(p)
        np.testing.assert_array_equal(a,b)
        self.assertGreater(b[0,loaded.pairs.index((0,6))],0)


if __name__=='__main__':unittest.main()
