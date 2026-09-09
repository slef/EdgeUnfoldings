from copy import deepcopy
from fractions import Fraction as F
import unittest
from n6.tests.test_cover import example
from n6.progress import audit

class ProgressTests(unittest.TestCase):
    def test_fraction_weights_cells_by_volume_and_keeps_missing_part(self):
        cover=example();lo,hi=map(F,cover['geometry']['parameter_box'][0])
        cover['tree']['value']=str(lo+(hi-lo)/4)
        cover['tree']['children'][1]={'kind':'unresolved'}
        report=audit(cover)
        self.assertEqual(report['result'],'verified_partial_region_coverage')
        self.assertEqual(report['certified_cells'],report['unresolved_cells'])
        self.assertEqual(report['certified_parameter_fraction'],'1/4')
        self.assertEqual(report['unresolved_parameter_fraction'],'3/4')

    def test_refining_a_cell_changes_counts_without_changing_coverage(self):
        cover=example();cover['tree']['children'][1]={'kind':'unresolved'}
        original=audit(cover)
        child=cover['tree']['children'][0];lo=F(cover['geometry']['parameter_box'][0][0]);hi=F(cover['tree']['value'])
        cover['tree']['children'][0]={'kind':'split','axis':0,'value':str((lo+hi)/2),'children':[deepcopy(child),deepcopy(child)]}
        refined=audit(cover)
        self.assertEqual(refined['certified_cells'],original['certified_cells']+1)
        self.assertEqual(refined['certified_parameter_fraction'],original['certified_parameter_fraction'])

    def test_a_label_does_not_replace_geometric_replay(self):
        cover=example();cover['tree']['children'][0]['pairs'].pop()
        with self.assertRaisesRegex(ValueError,'Missing face pairs'):audit(cover)

    def test_missing_child_cannot_be_counted_as_full_coverage(self):
        cover=example();cover['tree']['children'].pop()
        with self.assertRaisesRegex(ValueError,'exactly two'):audit(cover)

if __name__=='__main__':unittest.main()
