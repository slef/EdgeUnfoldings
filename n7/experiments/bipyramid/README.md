# Overnight floating discovery archive

These files record searches from 13 September 2026. They are discovery
programs, never proof predicates. Run from the worktree root with
`PYTHONPATH=.:n7/experiments/bipyramid`; their original output destinations
are `/private/tmp`, intentionally preserved in the archived source.

- Wide search: 45,000 attempts, 19,858 valid shapes, 2,581 two-patch
  rule checks. Its apparent largest-distance-sum **whole-net failure is
  a numerical artifact** in protected adjacent fan faces 5/6 at extreme
  aspect ratio. Do not interpret that JSON field as a counterexample.
- Receiver gate search: 23,746 attempts, 10,516 valid shapes, three
  weighted-gate examples subsequently converted to exact certificates.
- Receiver obstruction search: 120,000 attempts, 52,804 valid shapes,
  3,357 relevant patterns; it found no opposite preferences in that run.
- Blunter-pole search: 60,000 attempts, 26,389 valid shapes, 1,718 relevant
  patterns. Its second hit **does have opposite preferences and fails
  both receiver-plus-gap tests**. The initial summary overlooked this
  stronger fact. Rounded to one decimal and scaled by ten, it gives the
  exact integer example in `results/bipyramid-receiver-conflict.json`.

The failure to find a shape in one random run did not imply impossibility.
The exact replay modules in `n7/` supersede these numerical witnesses.
The finite proof examples and universal written lemmas have distinct scopes.

- Targeted chain search: 200,000 attempts, 139,137 valid shapes, 15,092
  chain-pattern shapes. Across eligible pole choices: 18,099 both-short,
  2,671 auxiliary bridges, 6,600 rejected by the auxiliary pole order,
  and 783 by the reduced graph. No residual overlap was found. These
  are overlapping choices, not disjoint shape counts. Classification
  tests graph and pole order before the endpoint maximum, so absence
  of the last label does not establish its automatic validity.
