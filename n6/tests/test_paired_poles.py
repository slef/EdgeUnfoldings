import json,unittest
from pathlib import Path
from n6.intervals import set_precision
from n6.paired_poles import select,wide_identities
from n6.octa_face_cap_examples import specification
from n6.minus_complementary_examples import specification as minus

class PairedPoleTests(unittest.TestCase):
    def setUp(self):set_precision(240)
    def test_wider_bounds_follow_from_all_sixteen_exact_identities(self):
        r=wide_identities();self.assertEqual(r['identities'],16)
        self.assertFalse(r['geometric_proof_formally_verified'])
    def test_all_three_fixed_pairs_on_regular_and_high_fan_octahedra(self):
        for name in ('regular-ties','high-fan'):
            pairs=((0,1),(2,4),(3,5))
            if name=='high-fan':pairs=((0,1),(2,4),(3,5))
            for pair in pairs:
                with self.subTest(name=name,pair=pair):
                    r=select(specification(name),pair)
                    self.assertEqual(sum(r['independent_whole_net']['pairs'].values()),28)
    def test_old_cap_failure_is_now_selected_without_a_cap_test(self):
        p=Path(__file__).resolve().parents[1]/'results/octa-unranked-cap-failure.certificate.json'
        r=select(json.loads(p.read_text()),(3,5))
        self.assertEqual((r['selection']['source'],r['selection']['slit']),(5,1))
        self.assertFalse(r['selection']['upper_face_cap_bounds_required'])
        self.assertEqual(sum(r['independent_whole_net']['pairs'].values()),28)
    def test_minus_fixed_pair_covers_old_switches_and_boundary(self):
        for kind,family in [('strict',False),('reflected',False),('boundary',False),('fallback',False),('fallback',True),('fallback_reflected',False)]:
            with self.subTest(kind=kind,family=family):
                r=select(minus(kind,family),(0,1))
                self.assertEqual(sum(r['independent_whole_net']['pairs'].values()),21)
                self.assertNotIn([2,3],r['selection']['cut_edges'])

if __name__=='__main__':unittest.main()
