# Seven-vertex unfolding investigation

Start with the [overview](index.html), the [arguments](ARGUMENTS.md), or the
[bipyramid patch proofs](BIPYRAMID_PATCHES.md). The HTML versions of the two
proof documents contain rendered mathematics and work without network access.

**Current result:** 34 graph types, 10 whole graph cases covered by established
theorems, 24 open. Twenty of the open types have a cofacial-core reduction.
For the pentagonal bipyramid, three of 15 necessary symbolic pattern classes
have written conditional existence proofs; the full graph remains open.
New arguments are under self-review. Numerical experiments and individual
coordinate certificates are never universal-proof premises.

## Isolation from the six-vertex and Lean work

This work starts at commit `5b21be4` on branch `codex/n7-unfolding`, in the
sibling worktree `EdgeUnfoldings-n7`. All new or edited tracked files are
under `n7/`. No `n6/`, `durer_small_n/`, root handoff, or Lean files are edited.
No n6 proof code is imported by these tools. The original checkout stays on
its own branch for the parallel Lean work.

Keep subsequent seven-vertex changes here. Read the six-vertex manuscript
as a dependency when useful, but do not update it or the other worktree as
part of an n7 experiment. Preserve earlier arguments and negative results.
Any later merge or publication should be a separate, explicitly reviewed action.
The existing GitHub Pages packager does not yet publish this new directory;
this initial overview is a local research page.

## Reproduce

Dependencies are listed in `requirements.txt`. Run from the worktree root,
with a Python environment containing them. The build of the two reading
pages additionally needs Pandoc on the command path.

```sh
python3 -B -m n7.catalogue --scan-trees
python3 -B -m n7.checks
python3 -B -m n7.build_overview
python3 -B -m unittest discover -s n7/tests -v
node n7/tests/overview.cjs
```

The saved `results/plantri.g6` was generated independently using the authors'
plantri 5.8 release, with `plantri -pg 7 n7.g6`. The source URL, archive hash,
and explicit bijection of its 34 outputs to our catalogue are retained in
`results/plantri-comparison.json`. No third-party executable is committed.

## Files and exact scope

| File | Purpose |
| --- | --- |
| `ARGUMENTS.md` | Complete graph decomposition; universal edge-star and dome cases; general cofacial-core proof; next targets |
| `BIPYRAMID_PATCHES.md` | Patch-family proofs, a general local Lemma L with explicit hypotheses, and the remaining pattern partition |
| `catalogue.py` | Atlas filtering, original facet cycles, all cut trees, and finite pair-reduction witnesses |
| `checks.py` | Independent tree counts, plantri matching, rational interval example, and exact symbolic-pattern census |
| `build_overview.py` | Offline graph diagrams, summary page, and mathematical reading pages |
| `results/catalogue.json` | All 34 graph records; selected candidate cuts and unresolved pairs |
| `results/core-completions.json` | All auxiliary triangulations of the four core graphs, with original-edge restrictions |
| `results/patch-patterns.json` | 121 labelled necessary patterns, 15 symmetry classes, and conditional proof status |
| `results/acute-bipyramid-box.json` | Exact hypotheses for one 21-coordinate box, not the whole graph |
| `results/validation.json` | 276 saved candidate audits replayed; 25,942 trees independently counted |

The nine focused Python tests cover enumeration, nonisomorphic graphs with
identical degrees, witness replay and rejection, the one-pair target, patch
counts, the exact box, every page link, and graph drawing crossings. The
separate script checks overview filters, cut visibility, and deep links.
These tests check implementations and finite applications; they are not
formal verification of the geometric arguments.

## Next session

1. Read the single unresolved pair for N7-A992: quadrilateral 0324 against
   triangle 036 in source-3 candidate with added cut 04.
2. Investigate the remaining two-inward-patch bipyramid patterns. The one-
   patch and single-intervening-convex-patch identities are particularly
   short starting points; no curvature ranking was needed for those proofs.
3. Treat cap attachment for N7-A1205 and uncut-diagonal restrictions for
   N7-A1167/N7-A1104 as separate missing lemmas.
4. Retain the initial overview history and keep graph counts distinct from
   conditional pattern counts, pair counts, and example certificates.
