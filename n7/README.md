# Seven-vertex unfolding investigation

Start with the [overview](index.html), the [arguments](ARGUMENTS.md), or the
[bipyramid patch proofs](BIPYRAMID_PATCHES.md), the dedicated [A992 case](A992.md),
its [cone proof](A992_CONES.md), the [R0 repair lemma](A992_R0.md), or the
[base-edge extension](A992_BASE_EDGES.md). The HTML versions of the eleven
proof documents contain rendered mathematics and work without network access.

**Latest focus:** [the remaining small-angle receiver pair](BIPYRAMID_CHAIN_PAIR.md).
The small-fan pocket is now excluded; the large-angle branch is proved.
An exact identity isolates the seventh vertex's correction to the n6
separator, and four rational examples replay the new applications.

**Overnight focus:** [new local and two-patch rules](BIPYRAMID_OVERNIGHT.md),
plus the [exact first collision](BIPYRAMID_COLLISION.md). The length-sum slit
settles all adjacent patch pairs universally. All two-inward-patch patterns
are covered when a pole curvature is at least π; three receiver patterns
also have the weighted gate `2κ_p + κ_q >= 2π`. The two-receiver conflicting
preference case and three/four-patch patterns remain open. Seven exact
examples and a 491-cell first-collision certificate are replayable.

The [insertion construction](BIPYRAMID_MORPH.md) and its
[interactive comparison](bipyramid-morph-demo.html) remain available.

**Current result:** 34 graph types, 10 whole graph cases covered by established
theorems, 24 open. Twenty of the open types have a cofacial-core reduction.
For the pentagonal bipyramid, three of 15 necessary symbolic pattern classes
have written conditional existence proofs; the full graph remains open.
For N7-A992, exact certificates refute the first fixed rule, both source-3
hinge choices together, and a longer-edge heuristic. A full-dimensional
11-parameter family is repaired by the new triangle attachment. The first
obstruction localizes to a five-vertex pyramid; the two-attachment conjecture
has three kinds of conditional pair implications. The new [cone proof](A992_CONES.md)
confines any Left failure to two explicit regimes. The [R0 repair lemma](A992_R0.md)
now proves E/135 throughout R0. The [base-edge extension](A992_BASE_EDGES.md)
also settles E/235 there when the two relevant hinges converge or are parallel.
Only E/Q remains in that family; divergent E/235 and all three R6 implications
remain open. Five of the six original cells are still not completely proved.
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
with a Python environment containing them. The build of the eleven reading
pages additionally needs Pandoc on the command path.

```sh
python3 -B -m n7.catalogue --scan-trees
python3 -B -m n7.checks
python3 -B -m n7.a992_exact
python3 -B -m n7.a992_figures
python3 -B -m n7.a992_cone_figures
python3 -B -m n7.r0_identity
python3 -B -m n7.r0_examples
python3 -B -m n7.r0_figures
python3 -B -m n7.base_edge_examples
python3 -B -m n7.base_edge_figures
python3 -B -m n7.bipyramid_morph
python3 -B -m n7.bipyramid_rule_checks
python3 -B -m n7.bipyramid_collision
python3 -B -m n7.bipyramid_receiver_conflict
python3 -B -m n7.bipyramid_receiver_identity
python3 -B -m n7.bipyramid_receiver_pairs
python3 -B -m n7.bipyramid_overnight_figures
python3 -B -m n7.bipyramid_morph_figures
python3 -B -m n7.build_overview
python3 -B -m unittest discover -s n7/tests -v
node n7/tests/overview.cjs
node n7/tests/morph.cjs
```

The saved `results/plantri.g6` was generated independently using the authors'
plantri 5.8 release, with `plantri -pg 7 n7.g6`. The source URL, archive hash,
and explicit bijection of its 34 outputs to our catalogue are retained in
`results/plantri-comparison.json`. No third-party executable is committed.

## Files and exact scope

| File | Purpose |
| --- | --- |
| `ARGUMENTS.md` | Complete graph decomposition; universal edge-star and dome cases; general cofacial-core proof; next targets |
| `BIPYRAMID_STAR_PATCH.md` | Shortest-patch comparison; every large-pole bipyramid proved; obtuse-corner and empty-region tests; exact four-tree failures |
| `BIPYRAMID_OVERNIGHT.md` | Universal local rule, two-patch large-gap and receiver-gate theorems, and curvature transfer |
| `BIPYRAMID_CHAIN_PAIR.md` | Small-fan exclusion, complete large-angle branch, wider-apex separator, and seventh-vertex correction |
| `BIPYRAMID_RECEIVERS.md` | Exact opposing receiver preferences, and a universal reduction of that pattern to two metric pairs |
| `BIPYRAMID_COLLISION.md` | Exact safe/overlapping transition on one insertion path, with a monotone circle-line proof |
| `OVERNIGHT_2026_09_13.md` | Overnight deadline, progress, discovery limits, and the next bounded investigation |
| `BIPYRAMID_MORPH.md` | Three deletion types, convex insertion, monotone curvature, tree lifting, exact failures, and the open continuation problem |
| `bipyramid_morph.py` | Exact replay of two insertion paths, minimum-curvature ordering, and a positive-area overlap |
| `bipyramid-morph-demo.html` | Offline slider showing both inserted solids and their nets; drawings are rounded illustrations |
| `BIPYRAMID_PATCHES.md` | Patch-family proofs, a general local Lemma L with explicit hypotheses, and the remaining pattern partition |
| `A992_BASE_EDGES.md` | E/235 proved for obtuse E and converging or parallel base hinges; divergent family still open |
| `A992_R0.md` | Obtuse-petal proof closing E/135 throughout R0; five conditional obligations remain |
| `r0_identity.py` | Exact coefficient check of the new positive angle identity |
| `A992_CONES.md` | Geometric proof settling Left outside two explicit obstruction regimes; exact sharp-4 example |
| `A992.md` | Exact failures, a five-vertex localization proof, and the remaining two-attachment obligations |
| `a992_exact.py` | Strict rational interval replay of overlap and successful repair certificates |
| `a992.py`, `a992_figures.py` | Floating discovery and figures; never proof predicates |
| `experiments/a992/` | Reproducible archived searches and their limitations |
| `catalogue.py` | Atlas filtering, original facet cycles, all cut trees, and finite pair-reduction witnesses |
| `checks.py` | Independent tree counts, plantri matching, rational interval example, and exact symbolic-pattern census |
| `build_overview.py` | Offline graph diagrams, summary page, and mathematical reading pages |
| `results/catalogue.json` | All 34 graph records; selected candidate cuts and unresolved pairs |
| `results/core-completions.json` | All auxiliary triangulations of the four core graphs, with original-edge restrictions |
| `results/patch-patterns.json` | 121 labelled necessary patterns, 15 symmetry classes, and conditional proof status |
| `results/acute-bipyramid-box.json` | Exact hypotheses for one 21-coordinate box, not the whole graph |
| `results/validation.json` | 276 saved candidate audits replayed; 25,942 trees independently counted |

The focused Python tests cover enumeration, nonisomorphic graphs with
identical degrees, witness replay and rejection, the one-pair target, patch
counts, the exact box, every page link, and graph drawing crossings. The
separate script checks overview filters, cut visibility, and deep links.
These tests check implementations and finite applications; they are not
formal verification of the geometric arguments.

## Next session

1. Read `OVERNIGHT_2026_09_13.md` and `BIPYRAMID_OVERNIGHT.md#next`.
   Read `BIPYRAMID_STAR_PATCH.md`: every pole-curvature-at-least-π case is now proved.
   Four shortest-patch endpoint trees can all fail outside the proved gates;
   do not assume that restricted rule universal. Work in the both-low-pole
   region, while also pursuing the small-angle configurations in `BIPYRAMID_CHAIN_PAIR.md#remaining`.
   Opposite receiver preferences and both receiver-plus-gap failures are
   now realized by an exact integer example with six safe nets. Do not
   try to prove those inequalities impossible. The original fixed
   insertion collision is also completely classified for its specified
   path. The other two receiver classes may admit stronger rules.
2. Keep the A992 results as a secondary route. Read `A992.md#next-lemma`. The fixed source-3 rule is refuted; do not
   restart its universal proof. Read `A992_CONES.md`, `A992_R0.md`, and `A992_BASE_EDGES.md`. Work on E/Q in R0, E/235 with divergent hinges,
   or one of the three remaining R6 implications
   for the Left-to-Right triangle attachment, using the five-vertex
   localization of the initial obstruction.
3. Investigate the remaining two-inward-patch bipyramid patterns. The one-
   patch and single-intervening-convex-patch identities are particularly
   short starting points; no curvature ranking was needed for those proofs.
4. Treat cap attachment for N7-A1205 and uncut-diagonal restrictions for
   N7-A1167/N7-A1104 as separate missing lemmas.
5. Retain the initial overview history and keep graph counts distinct from
   conditional pattern counts, pair counts, and example certificates.
