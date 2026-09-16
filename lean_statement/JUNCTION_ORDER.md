# Ordering the routes at a nonvertex junction

The planar wedge step needs the actual order of incoming and outgoing
source rays. This note records the part now checked and the exact next
connection. It does not assert global consistency of an unfolded surface.

## Actual route labels, retained by the chart

`CutVoronoiChart.source_routes` identifies its source set with copies that
represent final straight portions of actual shortest routes. Both existing
chart constructors now prove this property, in a face and across an
original edge. It is not an added hypothesis on a polyhedron.

[CutVoronoiRoutes.lean](SixVertexUnfolding/Geometry/CutVoronoiRoutes.lean)
proves a bijection from source copies to normalized shortest routes that
preserves the terminal coordinate formula. Finiteness gives one common
terminal parameter interval for all routes. At time `t < 1`, all their
chart points lie on the circle with radius

```
(1 - t) * surfaceDist source junction.
```

Distinct source copies give distinct points on this circle. This is the
actual local order of shortest-route approaches to the junction.

## Angular order and the cut rays it supplies

[CircularSourceOrder.lean](SixVertexUnfolding/Geometry/CircularSourceOrder.lean)
enumerates a finite circle of source copies by strictly increasing angles
in `[0, 2π)`. Consecutive entries have an empty open angular gap; the
last-to-first gap uses the next full turn.

[CircularVoronoiSectors.lean](SixVertexUnfolding/Geometry/CircularVoronoiSectors.lean)
proves that the ray bisecting any such gap has precisely its two endpoint
sources nearest. Every other source copy is strictly farther away. The
proof includes gaps greater than `π` and uses exact trigonometric distance
comparisons.

[JunctionSourceOrder.lean](SixVertexUnfolding/Geometry/JunctionSourceOrder.lean)
combines this angular enumeration with the actual route bijection and
common tail interval. Its `consecutive_cut_ray` and `closing_cut_ray`
map every sufficiently short positive portion of each gap-bisecting ray
into the actual multiple-route locus.

These facts are local to nonsource nonvertex points in the canonical
six-vertex models. They do not remove the separate universal-vertex
avoidance restriction.

## Exhaustion and actual incident edges

[CircularVoronoiRays.lean](SixVertexUnfolding/Geometry/CircularVoronoiRays.lean)
proves that the complete Voronoi boundary is the center together with the
listed positive gap rays. Before a gap midpoint the first source is uniquely
nearest; after it the second is uniquely nearest. Coverage by all circular
gaps excludes additional rays. Distinct listed rays meet only at the center.

[JunctionIncidence.lean](SixVertexUnfolding/Geometry/JunctionIncidence.lean)
identifies these rays with the actual incident edges. The proof first matches
both lists to the cut points on a sufficiently small circle.
`gap_rays_equiv_neighbors` then supplies one fixed bijection valid at every
smaller positive radius. Its mapped ray points lie in the corresponding
open graph edge. A connected trace avoiding graph vertices cannot change
edges, as proved in
[CutGraphOpenEdges.lean](SixVertexUnfolding/Geometry/CutGraphOpenEdges.lean).

Thus the two local obligations, exhaustion and actual edge incidence, are
**2/2 checked**. This is a bounded milestone, not a percentage of the full
star-unfolding proof.

## Actual branch pairs and common triangle placements

`CutVoronoiChart.local_distance` and `route_stability` retain the local
minimum-distance formula and the distance formula of nearby routes in the
same branch. Both face and original-edge constructors prove these fields
from existing results. They add no assumption on the input polyhedron.

[RouteBranchSeparation.lean](SixVertexUnfolding/Geometry/RouteBranchSeparation.lean)
proves that two distinct continuous branches cannot merge at a nonvertex
endpoint. [JunctionBranchSources.lean](SixVertexUnfolding/Geometry/JunctionBranchSources.lean)
then identifies their two limiting source copies with exactly the two
endpoints of the assigned angular gap. This includes actual route labels,
not just equality of cardinalities or distances.

[JunctionMetricTriangles.lean](SixVertexUnfolding/Geometry/JunctionMetricTriangles.lean)
places an entire incident metric kite in the common chart coordinates:
its base follows the assigned gap ray, and either prescribed ordering of
its two source labels is respected. The full metric profile follows from
one small sample and the squared-distance identity along a segment.

[JunctionTriangleLabels.lean](SixVertexUnfolding/Geometry/JunctionTriangleLabels.lean)
selects these motions with the actual limiting route labels. Two placements
with the same label have the same actual route and agree along its entire
length. This does not require the whole route to fit inside the local chart.

[JunctionTriangleJoin.lean](SixVertexUnfolding/Geometry/JunctionTriangleJoin.lean)
joins the two triangles bordering consecutive gaps using those already
chosen motions. Their actual surface intersection is the shared route;
their planar intersection is the corresponding radial segment. The joined
homeomorphism retains each original triangle map. No separate pairwise
reflection is chosen at this stage.

The focused obligations of branch-pair identification, metric placement,
and prescribed-motion two-triangle joining are **3/3 checked**.

## Simultaneous fan and the actual wedge step

[JunctionOrder.lean](SixVertexUnfolding/Geometry/JunctionOrder.lean) and
[JunctionFan.lean](SixVertexUnfolding/Geometry/JunctionFan.lean) construct
all incident developments with one chart, one circular order, and actual
route labels. The data are selected simultaneously; the quotient cut
surface is still separate work.

[JunctionWedgeStep.lean](SixVertexUnfolding/Geometry/JunctionWedgeStep.lean)
now derives the arm inequalities and applies the full kite-addition step
for any distinct incoming and outgoing edges. The closing gap and both
orders of the edges are covered by explicit full-turn shifts and rigid
coordinate changes. Its only remaining angle premise is the accumulated
budget using the actual metric kite's source angle.

[JunctionAngleSum.lean](SixVertexUnfolding/Geometry/JunctionAngleSum.lean)
proves that all incident triangle corners sum to exactly 2π. Each triangle
corner is half its gap; the gap widths telescope over a bijection with
actual neighboring edges. No ordering or chart assumption needs to be
supplied for an actual nonvertex tree vertex.

## Still required

The separate original-vertex cone argument is now checked.
[CutTreeConeCoverage.lean](SixVertexUnfolding/Geometry/CutTreeConeCoverage.lean)
discharges all five inequalities; `CutTreeSourceBudget` and
`CutTreePathBudget` give the total and simple-path source-angle bounds.
[CONE_BUDGET.md](CONE_BUDGET.md) records the actual geometric construction.

The updated wedge is now identified with the next incoming frame, using
the same motion that aligns both complete triangle developments. Whole
kites at a nonvertex junction are proved separate, and finite wedge-chain
iteration is checked. See [WEDGE_CHAINS.md](WEDGE_CHAINS.md).

Construct the global cut surface with distinct copies of the source and
star-cut rays, handle internal original-vertex junctions, and apply the
chain result to the entire surface partition. Whole-face transfer remains
open; see [STAR_NEXT.md](STAR_NEXT.md).
