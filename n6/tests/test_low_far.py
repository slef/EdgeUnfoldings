import copy
import unittest
from n6.intervals import set_precision
from n6.low_far import make_certificate,verify
from n6.low_far_examples import specification,check_strict_rank_failures
from n6.polycert import make_certificate as all_certificate,verify as all_pairs
from n6.selected_octahedron_examples import specification as selected_spec


class LowFarTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        set_precision(240);cls.cert=make_certificate(specification('point'))

    def test_three_checks_work_without_either_ranking(self):
        self.assertNotIn('pair_witnesses',self.cert)
        self.assertEqual(len(self.cert['local_pair_witnesses']),3)
        report=verify(self.cert)
        self.assertTrue(report['whole_net_nonoverlapping'])
        self.assertFalse(report['every_slit_lemma_F_proved'])
        self.assertEqual(report['far_pairs_implied_by_written_theorem'],6)
        self.assertTrue(check_strict_rank_failures(self.cert)['R_fails'])
        self.assertEqual(all_pairs(all_certificate(specification('point')))['result'],'verified')

    def test_full_coordinate_box_and_independent_all_pairs(self):
        spec=specification('family');cert=make_certificate(spec)
        self.assertEqual(verify(cert)['parameter_dimension'],18)
        self.assertTrue(check_strict_rank_failures(cert)['H_fails'])
        self.assertEqual(all_pairs(all_certificate(spec))['result'],'verified')

    def test_missing_duplicate_wrong_and_reversed_witnesses_rejected(self):
        cert=copy.deepcopy(self.cert);cert['local_pair_witnesses'].pop()
        with self.assertRaisesRegex(ValueError,'Missing local pair'):verify(cert)
        cert=copy.deepcopy(self.cert);cert['local_pair_witnesses'][1]=cert['local_pair_witnesses'][0]
        with self.assertRaisesRegex(ValueError,'Repeated or wrong local target'):verify(cert)
        cert=copy.deepcopy(self.cert);cert['local_pair_witnesses'][0]['faces']=[0,0]
        with self.assertRaisesRegex(ValueError,'Repeated or wrong local target'):verify(cert)
        cert=copy.deepcopy(self.cert);cert['local_pair_witnesses'][0]['edge'].reverse()
        with self.assertRaisesRegex(ValueError,'oriented face edge'):verify(cert)

    def test_curvature_above_pi_or_unresolved_not_accepted(self):
        with self.assertRaisesRegex(ValueError,'All-low curvature'):
            make_certificate(selected_spec('high-curvature'))
        # This is an exact full-dimensional box crossing pi, not evidence
        # that every one of its points has low curvature.
        with self.assertRaisesRegex(ValueError,'All-low curvature'):
            make_certificate(selected_spec('crossing-threshold'))

    def test_boundary_equality_is_accepted_when_exactly_certified(self):
        report=verify(make_certificate(selected_spec('curvature-equality')))
        self.assertIn('=',report['curvature_comparisons_with_pi'].values())

    def test_selection_and_cut_must_agree(self):
        cert=copy.deepcopy(self.cert);cert['selection']['slit_index']=0
        with self.assertRaisesRegex(ValueError,'Cuts disagree'):verify(cert)

    def test_actual_local_failure_under_H_is_rejected(self):
        from n6.low_local_failure import specification as failure_spec,make_certificate as failure_certificate,verify as check_failure,repair
        spec=failure_spec();failure=failure_certificate();report=check_failure(failure)
        self.assertTrue(report['all_six_far_pairs_safe'])
        self.assertFalse(report['refutes_every_slit_lemma_F'])
        self.assertEqual(report['nonoverlapping_pairs'],26)
        with self.assertRaisesRegex(ValueError,'unresolved'):make_certificate(spec)
        self.assertEqual(all_pairs(repair())['result'],'verified')
        incomplete=copy.deepcopy(failure);incomplete['nonoverlap_witnesses'].pop()
        with self.assertRaisesRegex(ValueError,'Missing face pairs'):check_failure(incomplete)


if __name__=='__main__':unittest.main()
