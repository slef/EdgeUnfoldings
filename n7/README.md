# Seven-vertex unfolding investigation

Start with the [overview](index.html), the [arguments](ARGUMENTS.md), or the
[bipyramid patch proofs](BIPYRAMID_PATCHES.md), the dedicated [A992 case](A992.md),
its [cone proof](A992_CONES.md), the [R0 repair lemma](A992_R0.md), or the
[base-edge extension](A992_BASE_EDGES.md). The HTML versions of the
proof documents contain rendered mathematics and work without network access.

**Current main result:** [the adjacent-run theorem](BIPYRAMID_ADJACENT.md)
completes the last two-inward class. Every pentagonal bipyramid with at
most two inward patches is now covered: **7/15** necessary symbolic
classes. Eight three/four-inward classes retain open parts. The adjacent
argument also works for any ring size. Earlier proofs are preserved below.

**Latest structural results:** the [supporting-plane theorem](BIPYRAMID_SOURCE_PLANE.md)
and stronger [local product rule](BIPYRAMID_PRODUCT_RULE.md) give sufficient
unfolding rules for any ring size and any patch pattern. The plane theorem
also shortens the large-pole and aligned-pole proofs; either aligned source
works at arbitrary heights. The [finite-switch insertion theorem](BIPYRAMID_SWITCH_INSERTION.md)
proves a tilted-axis family, with an exact minimum-curvature example and
one change of maximizing slit. [Explore the insertion](bipyramid-switch-demo.html).

The eight open classes now split into two pure-run conjectures (BBBCC,
BBBBC) and six classes with exact failures of the sufficient product test.
Three new mixed-block failures still have both maximal-slit nets exactly
certified safe. These are limits of the test, not counterexamples to unfolding.

**Earlier step:** [radial receiver lemmas](BIPYRAMID_RADIAL.md) close
FCFCC / BCBCC and FCCCB / BFCCC, and give a shorter proof of FCCBC.
That radial step raised the count to six; the adjacent theorem raises it to seven.
Four exact local examples check both lemmas in all three projection regimes;
five complete-net applications verify the rules independently.

**Earlier step:** [the complete opposing-chain rule](BIPYRAMID_CHAIN_RULE.md)
closes FCCBC / BCFCC with no curvature-order hypothesis. The new local
long-receiver lemma forces an acute fan apex and supplies the missing
separation bounds. Six exact applications exercise all three pole choices.
The [aligned-pole family](BIPYRAMID_ALIGNED.md) is proved at every height,
with one fixed tree throughout a six-to-seven insertion. The
[large-pole theorem](BIPYRAMID_STAR_PATCH.md) covers every pattern for any
ring size when either pole has curvature at least π.

**Earlier overnight step:** [new local and two-patch rules](BIPYRAMID_OVERNIGHT.md),
plus the [exact first collision](BIPYRAMID_COLLISION.md). The length-sum slit
settles all adjacent patch pairs universally. All two-inward-patch patterns
are covered when a pole curvature is at least π; three receiver patterns
also have the weighted gate `2κ_p + κ_q >= 2π`. The conflicting-receiver pattern has since been completed. Only the three/four-inward classes retain open parts. Seven exact
examples and a 491-cell first-collision certificate are replayable.

The [insertion construction](BIPYRAMID_MORPH.md) and its
[interactive comparison](bipyramid-morph-demo.html) remain available.

**Current result:** 34 graph types, 10 whole graph cases covered by established
theorems, 24 open. Twenty of the open types have a cofacial-core reduction.
For the pentagonal bipyramid, seven of 15 necessary symbolic pattern classes
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
with a Python environment containing them. The build of the reading
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
python3 -B -m n7.bipyramid_adjacent
python3 -B -m n7.bipyramid_radial
python3 -B -m n7.bipyramid_radial_figures
python3 -B -m n7.bipyramid_chain_rule
python3 -B -m n7.bipyramid_chain_figures
python3 -B -m n7.bipyramid_star_patch
python3 -B -m n7.bipyramid_aligned
python3 -B -m n7.bipyramid_four_bad_box
python3 -B -m n7.bipyramid_overnight_figures
python3 -B -m n7.bipyramid_morph_figures
python3 -B -m n7.build_overview
python3 -B -m unittest discover -s n7/tests -v
node n7/tests/overview.cjs
node n7/tests/morph.cjs
node n7/tests/aligned.cjs
```

The saved `results/plantri.g6` was generated independently using the authors'
plantri 5.8 release, with `plantri -pg 7 n7.g6`. The source URL, archive hash,
and explicit bijection of its 34 outputs to our catalogue are retained in
`results/plantri-comparison.json`. No third-party executable is committed.

## Files and exact scope

| File | Purpose |
| --- | --- |
| `ARGUMENTS.md` | Complete graph decomposition; universal edge-star and dome cases; general cofacial-core proof; next targets |
| `BIPYRAMID_ADJACENT.md` | Final two-inward class FFCCC / BBCCC; full pole-selection rule and proof, for any ring size |
| `BIPYRAMID_RADIAL.md` | Universal shield and cone-and-disk lemmas; complete Separated and Long Chain patterns; shorter Chain proof |
| `BIPYRAMID_CHAIN_RULE.md` | Complete FCCBC / BCFCC class, finite pole-selection rule, and local acute-fan lemma |
| `BIPYRAMID_ALIGNED.md` | Entire aligned-pole family; one fixed cut tree throughout lower-pole insertion from zero curvature |
| `bipyramid_four_bad_box.py` | Exact 21-coordinate CBBBB neighborhood, including nonplanar equators and displaced poles; all 45 face pairs certified |
| `bipyramid-aligned-demo.html` | Interactive illustration of the written all-height theorem, with a 3D solid and safe net |
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

1. Read the final checkpoint in `OVERNIGHT_2026_09_13.md`, then
   `BIPYRAMID_PRODUCT_RULE.md`. Try the pure runs BBBCC and BBBBC first:
   a common product-passing pole is conjectural. In the six other open
   classes, work with the actual overlap obligations; exact conflicts
   refute a universal common-passing-pole shortcut. The four-vertex
   restriction localizes these conflicts. Review the new universal
   proofs independently before treating them as established dependencies.
2. Keep the A992 results as a secondary route. Read `A992.md#next-lemma`. The fixed source-3 rule is refuted; do not
   restart its universal proof. Read `A992_CONES.md`, `A992_R0.md`, and `A992_BASE_EDGES.md`. Work on E/Q in R0, E/235 with divergent hinges,
   or one of the three remaining R6 implications
   for the Left-to-Right triangle attachment, using the five-vertex
   localization of the initial obstruction.
3. All two-inward bipyramid classes now have written complete proofs.
   Preserve them and the earlier reductions; the whole-class count is 7/15.
4. Treat cap attachment for N7-A1205 and uncut-diagonal restrictions for
   N7-A1167/N7-A1104 as separate missing lemmas.
5. Retain the initial overview history and keep graph counts distinct from
   conditional pattern counts, pair counts, and example certificates.

- [Ordered runs](BIPYRAMID_RUNS.html): a conditional theorem for any run length, with exact three- and four-inward applications. Common-pole existence remains open.

- [Source supporting plane](BIPYRAMID_SOURCE_PLANE.html): an any-ring-size theorem for every patch pattern under one geometric half-space condition; nonplanar examples included.

- [Local diagonal-product rule](BIPYRAMID_PRODUCT_RULE.html): a stronger sufficient criterion at inward corners, with exact successful applications and strict conflicts between the two pole choices.

- [Finite-switch insertion](BIPYRAMID_SWITCH_INSERTION.html): a whole tilted-axis family, a bound of twenty candidate slit changes at n=7, and an exact minimum-curvature three-inward example with one change. [Interactive model](bipyramid-switch-demo.html).
