# Archived discovery recipes for A992

These are numerical experiments, not proofs. Run from the worktree root with
`PYTHONPATH=.` and the dependencies in `n7/requirements.txt`. Each script has
a fixed seed and writes the correspondingly named JSON under `n7/results/`.
The candidate survey reuses failures from `python3 -B -m n7.a992` as initial
stress cases. Run that first if regenerating from scratch.

The scripts are retained as the actual chronological experiments, including
their initial sampling bounds and near-flat inconclusive results. Their
floating `valid` predicates and tolerances are discovery filters only.

| Recipe | Saved result |
| --- | --- |
| `python3 -B -m n7.a992 --samples 2500` | `a992-survey.json` |
| `candidate_survey.py` | `a992-candidate-survey.json` |
| `alternative_search.py` | `a992-alternative-search.json` |
| `two_petal_survey.py` | `a992-two-petal-survey.json` |
| `length_search.py` | `a992-length-rule-search.json` |
| `two_hinges_search.py` | `a992-two-hinges-search.json` |
| `three_hinges_search.py` | `a992-three-hinges-search.json` |

Reproducibility means the inputs, seeds, searches, and outputs are available;
floating optimization may differ with library/platform versions. The exact
counterexamples were separately rounded to rational parameters and certified.
Their verifier, `python3 -B -m n7.a992_exact`, replays strict rational inequalities
without depending on any optimizer result or tolerance.
