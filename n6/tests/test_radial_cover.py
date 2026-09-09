import copy,json,itertools
from pathlib import Path
import unittest
from n6.radial_cover import verify as verify_cover,radial_angle_bound,audit_failure
from n6.sector_cover import verify as verify_chord
from n6.polycert import verify
from n6.intervals import I,set_precision


class RadialCoverTests(unittest.TestCase):
    def setUp(self):
        set_precision(240);self.root=Path(__file__).resolve().parents[1]/'results'

    def test_triangle_angle_comparison_with_equality(self):
        rays={1:(1,1),2:(0,1),3:(-1,1)}
        for a,b in itertools.product(rays,repeat=2):
            self.assertEqual(radial_angle_bound(tuple(map(I,rays[a])),
                                               tuple(map(I,rays[b]))),a+2*b<=8)
        # omega=90°, nu=135° is equality; nu approaching 180° fails.
        self.assertTrue(radial_angle_bound((I(0),I(1)),(I(-1),I(1))))
        self.assertFalse(radial_angle_bound((I(0),I(1)),(I(-2),I(1))))

    def test_asymmetric_region_extends_the_chord_criterion(self):
        c=json.loads((self.root/'radial-cover-asymmetric-family.certificate.json').read_text())
        self.assertEqual(len(c['parameter_box']),15)
        report=verify_cover(c)
        self.assertEqual(report['result'],'verified_radial_cover_hypotheses')
        necessary=[r for r in report['routes'] if r['possible_shortest_path']]
        self.assertTrue(any(r['certified_methods']==['omega_plus_twice_nu_at_most_two_pi'] for r in necessary))
        self.assertEqual(verify(c)['result'],'verified')
        c['sector_cover']=copy.deepcopy(c['radial_cover'])
        with self.assertRaisesRegex(ValueError,'no certified short endpoint'):verify_chord(c)

    def test_old_short_edge_examples_are_still_covered(self):
        for regime in ('zero','one','two-adjacent','two-opposite','three'):
            c=json.loads((self.root/('short-edge-'+regime+'.certificate.json')).read_text())
            c['radial_cover']=copy.deepcopy(c['sector_cover'])
            self.assertEqual(verify_cover(c)['result'],'verified_radial_cover_hypotheses')

    def test_exact_radial_obstruction_is_rejected_at_its_sharpest_sector(self):
        c=json.loads((self.root/'sector-three-patch-radial-failure.certificate.json').read_text())
        c['radial_cover']=dict(source=1,sector_vertex=0,equator=[2,3,4,5])
        with self.assertRaisesRegex(ValueError,'no certified radial bound'):verify_cover(c)

    def test_all_sector_vertices_fail_the_sufficient_test_but_the_net_succeeds(self):
        c=json.loads((self.root/'radial-cover-insufficient.certificate.json').read_text())
        report=audit_failure(c)
        self.assertEqual(report['result'],'verified_failure_of_all_high_vertex_radial_covers')
        rows=report['vertices']
        self.assertEqual([r['vertex'] for r in rows if 'equator_edge' in r],[0,4,5])
        self.assertEqual(verify(c)['result'],'verified')

    def test_failure_audit_does_not_accept_a_covered_example(self):
        c=json.loads((self.root/'radial-cover-asymmetric-family.certificate.json').read_text())
        with self.assertRaisesRegex(ValueError,'No failing patch certified'):audit_failure(c)


if __name__=='__main__':unittest.main()
