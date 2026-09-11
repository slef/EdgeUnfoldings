import copy
import unittest

from n6.far_pair_examples import source
from n6.far_pairs import make_certificate, verify
from n6.intervals import set_precision


class FarPairReductionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        set_precision(240)
        cls.cert = make_certificate(source('apex-entry'))

    def test_only_two_pair_witnesses_certify_the_point(self):
        self.assertNotIn('pair_witnesses', self.cert)
        self.assertEqual(len(self.cert['far_pair_witnesses']), 2)
        report = verify(self.cert)
        self.assertTrue(report['whole_selected_net_nonoverlapping'])
        self.assertFalse(report['universal_lemma_F_proved'])
        self.assertEqual(report['conditionally_implied_far_pairs'], 4)
        first = report['small_fan_cases'][0]
        self.assertEqual(first['slit_far_vertex'], 'strictly_past_X')
        self.assertFalse(first['base_halfplane_proves_both_pairs'])

    def test_missing_target_rejected(self):
        cert = copy.deepcopy(self.cert)
        cert['far_pair_witnesses'].pop()
        with self.assertRaisesRegex(ValueError, 'Missing slit-side'):
            verify(cert)

    def test_duplicate_target_rejected(self):
        cert = copy.deepcopy(self.cert)
        cert['far_pair_witnesses'][1] = cert['far_pair_witnesses'][0]
        with self.assertRaisesRegex(ValueError, 'wrong slit-side'):
            verify(cert)

    def test_reverse_separator_rejected(self):
        cert = copy.deepcopy(self.cert)
        cert['far_pair_witnesses'][0]['edge'].reverse()
        with self.assertRaisesRegex(ValueError, 'oriented face edge'):
            verify(cert)

    def test_selection_cannot_be_changed_without_changing_cuts(self):
        cert = copy.deepcopy(self.cert)
        cert['selection']['slit_index'] = 1
        with self.assertRaisesRegex(ValueError, 'Cuts disagree'):
            verify(cert)

    def test_family_has_exact_separators(self):
        cert = make_certificate(source('apex-entry-family'))
        report = verify(cert)
        self.assertEqual(report['parameter_dimension'], 11)
        self.assertTrue(report['whole_selected_net_nonoverlapping'])

    def test_a_different_valid_cut_tree_still_needs_the_slit_ranking(self):
        cert = copy.deepcopy(self.cert)
        s = cert['selection']; s['slit_index'] = 1
        cert['cut_edges'] = [[s['apex'],u] for u in s['equator']]+[[s['antipode'],s['equator'][1]]]
        with self.assertRaisesRegex(ValueError, 'Curvature comparison'):
            verify(cert)

    def test_near_X_corollary_is_checked_on_a_whole_coordinate_box(self):
        cert = make_certificate(source('radial-family'))
        report = verify(cert)
        self.assertEqual(report['parameter_dimension'], 18)
        small = [t for t in report['small_fan_cases'] if t['fan_angle_sum']=='<']
        self.assertEqual(len(small), 1)
        self.assertEqual(small[0]['slit_far_vertex'], 'at_or_before_X')
        self.assertTrue(small[0]['base_halfplane_proves_both_pairs'])


if __name__ == '__main__':
    unittest.main()
