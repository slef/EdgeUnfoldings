import copy,json,unittest
from fractions import Fraction as F
from n7.bipyramid_morph import ROOT,I,exact_points
from n7.bipyramid_rule_checks import replay_saved as replay_rules,receiver_gate,certify as certify_rules
from n7.bipyramid_collision import replay_saved as replay_collision,certify as certify_collision

class OvernightChecks(unittest.TestCase):
 def test_exact_opposing_receiver_preferences(self):
  from n7.bipyramid_receiver_conflict import replay_saved
  result=replay_saved();self.assertEqual(result['conflicting_receiver_plus_gap_tests'],2);self.assertEqual(result['certified_safe_nets'],6)

 def test_seven_exact_rule_examples(self):
  result=replay_rules();self.assertEqual(result['exact_examples'],7);self.assertEqual(result['local_pairs_checked'],21)
  rows=json.loads((ROOT/'results/bipyramid-two-gap.json').read_text())['examples']
  self.assertEqual(sum(r['certificate']['choice']['branch']=='switch-pole' for r in rows),1)
  self.assertEqual(sum('weighted' in r['certificate']['choice']['curvature_gate']['kind'] for r in rows),3)
  for row in rows:self.assertEqual(row['certificate']['fan_pairs']+len(row['certificate']['strict_separators']),45)
 def test_small_poles_do_not_automatically_pass_the_gate(self):
  row=json.loads((ROOT/'results/bipyramid-morph.json').read_text())['examples'][1]
  p=[[I.bounds(x) for x in v] for v in exact_points(row['points'])]
  for pole in(5,6):
   with self.assertRaises(ValueError):receiver_gate(p,pole)
 def test_first_collision_whole_interval_replay(self):
  result=replay_collision();self.assertEqual(result['cells'],491);self.assertEqual(result['nonlocal_pairs'],15)
  a,b=map(F,result['critical_bracket']);self.assertEqual(b-a,F(1,10**7))
 def test_incorrect_contact_bracket_is_rejected(self):
  spec=json.loads((ROOT/'results/bipyramid-first-collision.json').read_text())
  spec['critical_bracket']=['1/10','1/5']
  with self.assertRaises(ValueError):certify_collision(spec)
 def test_collision_cover_must_have_no_gap(self):
  spec=json.loads((ROOT/'results/bipyramid-first-collision.json').read_text());spec['cells'].pop(5)
  with self.assertRaises(ValueError):certify_collision(spec)

if __name__=='__main__':unittest.main()
