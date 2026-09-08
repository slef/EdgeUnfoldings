import unittest
from n6.trees import thesis_family,all_trees,degree_four_stars
from n6.families import PRISM_FACES,MINUS_FACES

FACES=((0,1,2),(0,3,1),(1,5,2),(0,2,4),(1,3,5),(2,5,4),(0,4,3),(3,4,5))


class ThesisFamilyTests(unittest.TestCase):
    def test_original_edge_star_families_retain_polygonal_facets(self):
        for faces,count in ((PRISM_FACES,6),(MINUS_FACES,14),(FACES,24)):
            family=degree_four_stars(faces)
            self.assertEqual(len(family),count)
            all_cuts={tuple(t['cuts']) for t in all_trees(faces)}
            self.assertTrue(all(tuple(t['cuts']) in all_cuts for t in family))

    def test_complete_cyclic_three_arm_family_is_distinct_from_nearstars(self):
        family=thesis_family(FACES)
        self.assertEqual(len(family),48)
        all_cuts={tuple(t['cuts']) for t in all_trees(FACES)}
        for tree in family:
            self.assertIn(tuple(tree['cuts']),all_cuts)
            self.assertEqual(len(tree['pairs']),11)
            degrees=[sum(v in e for e in tree['cuts']) for v in range(6)]
            self.assertEqual(sorted(degrees),[1,1,1,2,2,3])


if __name__=='__main__':unittest.main()
