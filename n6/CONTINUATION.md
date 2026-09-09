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
