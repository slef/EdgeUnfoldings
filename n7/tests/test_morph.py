"""Replay the interval families and reject invalid geometric claims."""
import copy
import json
from fractions import Fraction as F
import unittest
from n7.bipyramid_morph import ROOT,FACES,certify,check_net,develop,exact_points,inside,minimum,replay_saved

class MorphChecks(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.rows=json.loads((ROOT/'results/bipyramid-morph.json').read_text())['examples']
 def test_replay_entire_paths(self):
  result=replay_saved()
  self.assertEqual(result['examples'],2)
  self.assertEqual(result['closed_interval_cells'],264)
  self.assertEqual(result['minimum_curvature_comparisons'],12)
 def test_unchanged_initial_tree_really_fails(self):
  row=self.rows[1];p=exact_points(row['points'])
  with self.assertRaises(ValueError):check_net(p,row['initial_cut'])
  net=develop(p,row['initial_cut'])
  for i in row['overlap_pair']:
   self.assertEqual(len(inside(net[i],list(map(F,row['overlap_witness'])))),3)
  with self.assertRaises(ValueError):inside(net[row['overlap_pair'][0]],[F(0),F(0)])
 def test_minimum_is_not_merely_a_rounded_comparison(self):
  for row in self.rows:
   p=exact_points(row['points']);self.assertEqual(len(minimum(p,row['inserted_vertex'])),6)
   with self.assertRaises(ValueError):minimum(p,(row['inserted_vertex']+1)%5)
 def test_invalid_cut_is_rejected(self):
  row=self.rows[0];p=exact_points(row['points'])
  with self.assertRaises(ValueError):develop(p,row['initial_cut'][:-1]+[[5,6]])
  with self.assertRaises(ValueError):develop(p,row['initial_cut'][:-1])
 def test_a_gap_in_the_cover_is_rejected(self):
  row=copy.deepcopy(self.rows[0]);row['cover'][0]['cells'].pop(2)
  with self.assertRaises(ValueError):certify(row)
 def test_wrong_reduction_is_rejected(self):
  row=copy.deepcopy(self.rows[0]);row['subdivision_edge']=[4,1]
  with self.assertRaises(ValueError):certify(row)
 def test_overlarge_parameter_box_is_not_assumed_safe(self):
  row=copy.deepcopy(self.rows[0]);row['cover'][0]['cells']=[['0','1']]
  # This interval enclosure is too coarse; subdivision is material to the proof.
  with self.assertRaises(ValueError):certify(row)

if __name__=='__main__':unittest.main()
