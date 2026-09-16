# Six-vertex proof status

The main theorem is unfinished. Complete Lean proofs now cover every convex
polyhedron with at most five vertices, every convex pyramid, every convex
octahedron, every octahedron-minus-edge polyhedron, and every ordinary triangular
prism. The more general theorem for every convex dome is also proved. The completed
universal-source star construction now covers every polyhedron with at most
six vertices having a universal vertex. The definitions and
statement are unchanged. The sole `sorry` is in the target Statement file.

## Exact remaining cases

[SixVertexRemaining.lean](SixVertexUnfolding/SixVertexRemaining.lean) supplies
the earlier two-family reduction. The proof in `Statement.lean` now closes
its universal-vertex branch using
[UniversalStarUnfolding.lean](SixVertexUnfolding/Geometry/UniversalStarUnfolding.lean).
Only the prism-with-diagonal branch remains unfinished: exactly six
vertices, with triangular or quadrilateral original facets.

The prism-with-diagonal case is also proved in the curvature region
`κ₁ ≤ κ₀` and `κ₄ ≤ κ₅`, including equality. Its degree-four sources are 0 and 5
in the canonical labels. Comparing `κ₂` and `κ₃` chooses an original slit and
keeps both quadrilaterals whole. See
[PrismDiagonalSelection.lean](SixVertexUnfolding/PrismDiagonalSelection.lean).
The larger regions in [PrismDiagonalRegions.lean](SixVertexUnfolding/PrismDiagonalRegions.lean)
allow source 0 whenever κ₁ ≤ κ₀ and κ₂ ≤ max(κ₃, κ₄, κ₅), or source 5 whenever
κ₄ ≤ κ₅ and κ₃ ≤ max(κ₀, κ₁, κ₂). Thus one eligible source suffices, even when
the other endpoint is not the sharper pole. These are theorems for their
stated regions, not the complete graph family.

## Completed graph and facet classification

| Original graph | Missing pairs in the canonical labels | Whole original facets |
| --- | --- | --- |
| Octahedron | 01, 23, 45 | 8 triangles |
| Octahedron minus one edge | 01, 12, 23, 45 | 6 triangles, 1 quadrilateral |
| Prism with a diagonal | 01, 12, 23, 34, 45 | 4 triangles, 2 quadrilaterals |
| Triangular prism | 01, 12, 23, 34, 45, 05 | 2 triangles, 3 quadrilaterals |

These names impose no symmetry, metric regularity, or parallelism.
[SixVertexGraphs.lean](SixVertexUnfolding/Geometry/SixVertexGraphs.lean) derives
the labels from the actual geometric edge graph.
[SixVertexFacets.lean](SixVertexUnfolding/Geometry/SixVertexFacets.lean) proves
that the explicit lists are exactly the whole supporting facets.

The proof establishes minimum degree three, connectivity after deleting any
two vertices, and the two-facets-per-edge incidence rule directly from the
public convex-hull definition. A geometric double count excludes two triples
with all nine cross-edges. Complementary degree bounds and a finite relabeling
then give the four graphs. Facet incidences, including uniqueness of a facet
containing a nonedge pair, determine their face lists. No planar embedding,
external graph certificate, or native evaluation is assumed.

## Completed common development

The common subdivision has eight nondegenerate spatial triangles with actual
original carrier facets. Their unions recover every whole facet. Angles are
Mathlib Euclidean angles of the original spatial vertices. The six angular
deficits are positive and sum to `4π`; strict closed-link inequalities follow
from the transverse vertex figures, including flat auxiliary corners.

A sharper pole and a maximum-curvature equator slit determine the development.
Four fan triangles use cumulative polar angles; four petals attach outward.
The seven hinges match on whole segments. All **28/28 unordered triangle
pairs** have disjoint interiors:
[OctahedralAllPairs.lean](SixVertexUnfolding/Geometry/OctahedralAllPairs.lean).
There are no remaining pair-comparison premises in this result.

Local separators, both remote finite-cut exclusions, and the opposite-petal
Cases A and B are complete. The small-fan pocket argument is complete in both
orientations as well. Its constructed interior seeds give fan and whole-patch
containment. The contained fan fixes the boundary orientation. Four clockwise
corner angles sum to `2π`, while complementary petal corners and the exact
curvature identities force a contradiction. A separate six-sided polygon
after excision is unnecessary. See [POCKET_NEXT.md](POCKET_NEXT.md) for the map.

[OctahedronComplete.lean](SixVertexUnfolding/OctahedronComplete.lean) assembles
the complete original-edge octahedron unfolding. The wrapper
`every_convex_octahedron` in SixVertexRemaining needs no separate facet-size
premise.

## Completed whole-face reassembly

[QuadrilateralPlacementAgreement.lean](SixVertexUnfolding/Geometry/QuadrilateralPlacementAgreement.lean)
proves that the two rigid halves of a quadrilateral agree on its whole facet
when they meet outward across their flat diagonal.
[FlatPetalAgreement.lean](SixVertexUnfolding/Geometry/FlatPetalAgreement.lean)
and [FlatFanAgreement.lean](SixVertexUnfolding/Geometry/FlatFanAgreement.lean)
apply this to both kinds of retained subdivision hinge.

[SubdivisionCertificate.lean](SixVertexUnfolding/Geometry/SubdivisionCertificate.lean)
chooses one placement per whole face, contracts flat hinges, and retains a
spanning tree of original edges. The reassembled faces inherit the 28 proved
triangle separations. No auxiliary diagonal is cut.

[MinusEdge.lean](SixVertexUnfolding/MinusEdge.lean) chooses the sharper of poles
4 and 5. Its only repeated carrier is an attached fan-petal pair. The result
is a complete public `HasEdgeUnfolding` theorem for the whole original solid.
[OriginalCutSelection.lean](SixVertexUnfolding/OriginalCutSelection.lean)
provides the general selected-development certificate whenever all five cuts
are original edges.

## Ordinary prism and general domes: complete

[DomeComplete.lean](SixVertexUnfolding/Geometry/DomeComplete.lean) proves a
whole-face unfolding for every convex polyhedron with a facet adjacent to
all the others. [PrismComplete.lean](SixVertexUnfolding/PrismComplete.lean)
applies this to every ordinary triangular prism, without metric restrictions.
All **10/10 whole-face comparisons** are complete.

Parallel hinges give disjoint exterior halfplanes. Nonparallel extended
hinges meet at a virtual corner. The normalized support equations construct
an auxiliary point on both petal planes strictly inside the base halfspace.
The whole facets lie in the resulting corner cones, separated by a bisector
between the copied auxiliary points. Every needed plane membership, support
sign, extended rigidity, hinge agreement, and outwardness is proved.
[DOMES_NEXT.md](DOMES_NEXT.md) gives the full map.

## Shortest original source cuts: complete premises

[SurfacePaths.lean](SixVertexUnfolding/Geometry/SurfacePaths.lean) defines an
actual continuous boundary path and measures its arc length with Mathlib's
total variation. Every path is at least as long as its Euclidean chord, and
a straight path within a whole facet attains that bound. This proves the
shortest-path claim for original edges and straight face diagonals against
all continuous surface paths, including paths of infinite length.

[SixVertexStarCuts.lean](SixVertexUnfolding/Geometry/SixVertexStarCuts.lean)
proves that a universal vertex supplies a spanning tree of five original
shortest cuts, whose segments intersect only at their common source.
The complete universal-source star development, including nonoverlap,
local metric, connectivity, polygonal boundary, and whole-face conversion,
is now proved. Read `UniversalStarEmbedding` and `UniversalStarUnfolding`;
[STAR_NEXT.md](STAR_NEXT.md) records the exact scope.

## General shortest routes: existence and finite subdivision complete

[ShortestSurfacePaths.lean](SixVertexUnfolding/Geometry/ShortestSurfacePaths.lean)
proves existence for arbitrary boundary endpoints. Finite routes come from
facet walks; arc-length reparameterization gives a common speed bound;
Arzelà–Ascoli and lower semicontinuity of total variation give a minimizer.
Reparameterizing shorter competitors removes the auxiliary speed restriction.
Infinite-length competitors are included in the final comparison.

[ShortestFaceSubdivision.lean](SixVertexUnfolding/Geometry/ShortestFaceSubdivision.lean)
proves that each shortest route has finitely many straight portions in whole
original facets. The key fact is that a shortest portion between cofacial
points stays on its chord, so each visited face occupies one closed interval.
[ShortestSimplePaths.lean](SixVertexUnfolding/Geometry/ShortestSimplePaths.lean)
proves constant arc speed and injectivity for a chosen shortest path between
distinct endpoints. Zero-length paths and pauses in the original competitors
are handled. See [SHORTEST_PATHS.md](SHORTEST_PATHS.md).

Local continuation across edges is now also proved, together with flat metric
charts at all nonvertex points, affine coordinate formulas for shortest
routes, and local nonbranching. [LOCAL_GEODESICS.md](LOCAL_GEODESICS.md) gives
the proof map. Intermediate vertices are excluded for all polyhedra with
at most six vertices and triangular/quadrilateral faces, including the
universal-vertex family, so global nonbranching has no avoidance premise
in this scope. [CUT_LOCUS_FOUNDATIONS.md](CUT_LOCUS_FOUNDATIONS.md) maps the actual
local distance minimum and exact Voronoi description in faces and across
original edges. Junctions are now proved finite globally. Outside them and
original vertices, the cut has actual local intervals that preserve intrinsic
distance and cover nearby multiple-route targets. The explicit cut set is
compact and its complement is contractible. Its exact finite segment
decomposition and embedded graph subdivision are now checked, including
disjointness of distinct open graph edges. A continuous terminal-ray
retraction now proves the cut set path connected and contractible; the finite
embedded graph is connected. The cut set also equals exactly the closure of
multiple-route targets, including at original vertices. The graph is now
proved acyclic, and every leaf is proved to be an original vertex. The
radial partition is now constructed: continuous, disjoint open-edge strips
and finitely many tree-vertex rays cover the boundary outside the source and
cut set. Both closed strips for every edge now have actual planar triangle
developments, with correct radial lengths and distance preservation on
convex face and flat-chart patches. Open strips are open in the boundary
and correspond exactly to triangle interiors. Each local flat disk develops
by one rigid planar motion, including at original hinge interiors. Two
successive strips sharing an endpoint route now have one joined planar
homeomorphism; the corresponding triangles meet exactly along that ray.
The actual nonvertex junction fans and opposite-edge triangle agreement
are now constructed. The original cone inequalities and total/simple-path
source-angle budgets are proved. Wedge frame compatibility, first-kite
containment, finite region iteration, and terminal exclusion are checked,
with actual applications at one and two junctions. See
[WEDGE_CHAINS.md](WEDGE_CHAINS.md). The complete global surface construction
and whole-face transfer are now proved for the universal-source case; see
[GLOBAL_ASSEMBLY.md](GLOBAL_ASSEMBLY.md) and [STAR_NEXT.md](STAR_NEXT.md).
Internal original-vertex junctions for arbitrary sources remain outside that scope. This closes the universal-vertex family; no overall effort percentage is asserted.

## Verification and remaining work

All proved modules are imported by the library root and checked with the
pinned Lean compiler. The axiom audit traverses every project declaration,
including private helpers, and accepts only `propext`, `Classical.choice`, and
`Quot.sound`. The unfinished Statement is checked separately. README records
the final verified counts for this run.

The remaining main-theorem work is the prism-with-diagonal branch outside
the proved curvature regions. The required universal-source star theorem
is now proved rather than imported as an axiom. The single remaining
`sorry` represents that separate unfinished branch.
