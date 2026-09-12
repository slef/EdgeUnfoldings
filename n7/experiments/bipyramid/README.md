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


## Second overnight pass

The six additional searches are discovery only. They are archived without
rewriting their original temporary output paths; run with the repository
and this experiment directory on PYTHONPATH and inspect the explicit paths.

- `n7_pair_class_search`: 350,000 attempts, 124,043 valid sampled shapes,
  4,916 relevant opposing-chain shapes with both poles below π. No missing
  local-separator case found. This is not proof or coverage of metric space.
- `n7_chain_adversary` and `n7_chain_cobyla`: constrained floating attempts
  to break the wide-apex condition; no rigorous bound follows from outcomes.
- `n7_chain_gate_cover`: five sampled shapes where the only eligible chain
  pole has a negative seventh-vertex correction. A naive pole swap cannot
  be presumed to supply that sufficient gate. These five are not exact
  certificates; the saved local-pair data have a separate exact negative-H
  example that still passes the wider separator.
- `n7_star_patch_search`: discovers both proved-gate examples and failures
  of all four shortest-patch endpoint choices. Two failures were converted
  to exact certificates in `results/bipyramid-star-patch.json`.
- `n7_star_high_stress`: 200,000 attempts, 86,106 valid samples, 67,654 with
  a pole above π; no sampled failure of the separately written theorem.
  Includes 667 four-inward samples. Counts are discovery diagnostics only.

The universal results are in BIPYRAMID_CHAIN_PAIR.md and
BIPYRAMID_STAR_PATCH.md, not in these search statistics.
