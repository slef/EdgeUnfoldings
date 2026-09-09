# Latest continuation: minus-edge patterns

9 September 2026. [MINUS_PAIR.md](MINUS_PAIR.md) records a new two-tree
conjecture, a two-fan interpretation, exact switching examples, and a complete
16-cell certificate using one fixed tree on the same ±0.05 box. The earlier
certificate used nine trees and 409 cells. The domain is unchanged. The
universal two-tree statement remains open; 33,000 samples and 150 directed
starts are numerical evidence only. Its simultaneous-failure cases reduce
combinatorially to 28 symmetry classes, none yet excluded as a whole.

The earlier sessions are retained below.

---

# Second continuation on 9 September 2026

The overview was updated first, and the additional research hour began at
approximately 02:05 UTC. The full n=6 theorem remains open. The main new exact
result rules out a stronger intermediate claim without refuting the proposed
unfolding itself. Earlier progress is retained below.

## New exact results

- **Individual-apex exclusion is false for actual convex octahedra.** Six
  small integer-coordinate vertices satisfy H and R, strict Case B, and
  `Sigma_W+a<pi`; one outer apex and its far vertex pass into the relevant
  half-plane. The other petal remains outside, and all 28 pairs of the selected
  net are certified simple. An eleven-parameter closed box of radius `1/1000`
  has the same verified behavior. [CASE_PARTITION.md](CASE_PARTITION.md)
  gives the coordinates, orientation, figure, and exact replay commands.
  This does not settle the distinct remote-apex orientation.
- **Global metric closure is an additional necessary condition.** An exact
  intrinsic metric passes shared triangle lengths, positive curvatures, all
  six strict convex-vertex cone conditions, and H/R. Nevertheless, a complete
  five-interval certificate proves that it cannot be the original edges of
  a strictly convex octahedron. [AXIS_CLOSURE.md](AXIS_CLOSURE.md) derives the
  necessary equations and documents the verifier. No sufficiency claim is made.
- **Distance resolves the known local angular obstruction at that example.**
  On every shared ray, its petal starts at least `1217/1000` as far from w as
  the opposite fan's outer edge. Three exact inequalities establish this bound.
  [LEMMA_L.md](LEMMA_L.md) explains the clipped-triangle argument. L universally
  remains open. The closest candidate from the new coordinate search is also
  exactly certified nonoverlapping after rational reconstruction at 320 bits.
- **Prism path rules need a genuine choice.** Both quadrilateral routes at a
  fixed degree-four apex can fail. In a smaller example, the shorter route
  at the strictly sharper degree-four apex fails while the longer route gives
  a certified simple net. See [PRISM_DIAGONAL.md](PRISM_DIAGONAL.md). Neither
  example refutes the conditional reduction or the existence of an unfolding.

## Numerical exploration and unresolved queries

A reproducible coordinate optimizer retains the actual octahedron geometry,
H/R comparisons, and explicit support and azimuth guards. Ten-minute runs
made 2,112 local-search attempts and 971 joint-petal reach attempts in the
remote/slit-3 orientation. A further seven-minute run made 702 joint-reach
attempts in slit 0; neither orientation produced a candidate with positive
joint reach within these guarded searches. The saved
reports state their coordinate bounds and guards. The best local near-contact
candidate was rechecked exactly; its selected net is simple. No search absence
is treated as a theorem, and no numerical lower margin is claimed uniform.

The best joint-reach candidates are limited by the imposed support guard:
their minimum normalized supporting-plane clearance is approximately 1e-5.
Their fan-angle sums approach pi from below (gaps about 1.27e-4 and 2.88e-5
radians). In both, the far vertices approach the wedge crossing, while the
apex reach scores stay substantially negative. Thus these two optimizations
point toward nearly flat shapes near the already-proved cone boundary, not
toward both apices entering together. This is diagnostic numerical evidence
only; it suggests treating this boundary separately in a future proof and
explains why the observed negative score cannot be taken as a uniform bound.

The symbolic intrinsic search now supports axis closure. Two versions returned
`unknown` because of the 1 GB memory limit, after about 159 and 44 seconds.
The second version uses lower-degree opposite-arc equations and a shorter
angle target. Neither outcome proves the remaining bound.

For the prism, 50,000 samples found no failure of the four quadrilateral-route
trees. A separate 60,000-sample run found no failure when keeping both routes
at the sharper degree-four apex. Always choosing the shorter route failed
395 times, and one such failure was independently certified with integer
coordinates. Only the latter exact check proves that specific rule false.

## Overview and verification

The top notes are now retained in a collapsed history and repeated, filtered,
with their relevant results. Result links navigate and scroll to the actual
explanation, including repeated clicks on the currently selected result.
The cone proof, 409-region minus-edge certificate, 443-region prism certificate,
and remaining obligations have plain-language scope explanations. The original
illustrative prism remains first on its page. The new apex-entry example has
both a scientific net diagram and a matching interactive 3D model.

All **77 tests pass**, including the new point/region counterexamples, five-cell
nonclosure certificate, positive closure controls, and rejected tampered
certificates. The navigation regression passes; code-level checks render all
24 models and verify the thesis/prism controls and original prism ordering.
Every local file link resolves. These are code-level UI checks, not a claim of
interactive browser verification. The rebuilt eleven-page proof PDF was
rendered and visually checked before being saved.

## Next obligations

The individual-apex shortcut must be replaced by a joint constraint: when one
petal reaches the possible-meeting wedge, what prevents the other from meeting
it? Keep the slit-side and remote orientations explicit. For L, use distances
rather than requiring disjoint directions. For the prism, investigate both
quadrilateral paths at the sharper degree-four apex; length minimization alone
is false. For complete computational coverage, an exhaustive domain reduction
and treatment of degeneracies remain missing. The bounded region certificates
continue to prove exactly their stated domains.

---

# Continuation on 9 September 2026

The requested one-hour search began at approximately 00:12 UTC. Independent
verification and final packaging continued afterward. The full n=6 theorem,
Lemma L, and the remaining small-fan-angle Case B bound remain open.

## Independently verified progress

- **Wider original-facet coverage.** Every parameter in the ten-parameter
  octahedron-minus-edge chart may now vary independently by `1/20` about
  `(1,1,0,1,3/4,1/4,1,1/4,3/4,1)`. The 409-region cover passes independent
  replay, with nine trees and all 8,589 face-pair checks. See
  [REGION_COVER.md](REGION_COVER.md). This is an exact theorem about that closed
  box, not universal coverage of the combinatorial type.
- **A stronger obstruction to an angular proof of L.** An integer-coordinate
  convex octahedron satisfies H and R, yet one ray from w passes through both
  interiors of a local petal/fan pair at different distances. Every line through
  w fails to separate that pair. All 28 pairs of the same net are independently
  certified nonoverlapping. See [LEMMA_L.md](LEMMA_L.md) and its new diagram.
- **Metric compatibility made explicit.** The earlier rational angle model
  cannot close either spoke cycle. The new sine-rule equations characterize
  shared-edge compatibility of the eight triangles. A separate exact intrinsic
  metric satisfies the rankings but violates necessary convex-vertex cone
  inequalities. These distinguish two inadequate relaxations; neither witness
  disproves the geometric conjecture. See [INTRINSIC_METRIC.md](INTRINSIC_METRIC.md).

## Search and verification improvements

The wider cover was completed by overlaying complementary partial searches,
then resolving only their remaining cells. Candidate leaf counts are now
accompanied by exact parameter-volume fractions. Neither label counts nor
volume bookkeeping substitute for independent geometric replay.

The exact checker retains linear correlations when a norm is provably the
absolute value of one coordinate. An experimental affine-coefficient split
rule performed worse on this box and remains optional. Trying all 224 trees
on the unsplit wider root did not produce a single-box certificate; this was
an inconclusive interval calculation, not a proof of overlap.

The two intrinsic nonlinear queries timed out: approximately 904 seconds for
the lifted slit-3 query and 695 seconds for the unlifted slit-0 query. They
prove no universal bound. The driver now reuses the existing separate-process
time and memory guard; a short-limit check confirmed an explicit unresolved
termination result.

All **64 tests pass**. Overview checks render every section and all 23 existing
3D models, including the thesis and prism controls. The original illustrative
prism still appears before its reduction and failure example. The updated
overview includes the new L diagram and exact coverage scope.

## Next mathematical priorities

For L, look for a separator whose position depends on distances, or compare
radial intervals directly; disjoint angular sectors around w are too strong.
For Case B, retain both shared-edge compatibility and the convex-vertex cone
conditions, and state which triple/slit orientation is being treated. For
global computational coverage, the outstanding issue is an exhaustive domain
reduction, including near-degenerate limits; enlarging one local box does not
settle that issue.
