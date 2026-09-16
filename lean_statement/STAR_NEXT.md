# Star unfolding: current proved result and next gap

Checkpoint: 16 September 2026, 16:42 UTC.
**The six-vertex universal-source star theorem is proved.**
The arbitrary-source star theorem is not claimed. Public definitions and
the target theorem statement are unchanged.

The actual cut tree, covering triangles, source-angle budget, global
nonoverlap, retained-surface gluing, inverse disks, local intrinsic metric,
connectivity, and polygonal boundary are all checked. The whole-face
conversion now also produces the public `HasEdgeUnfolding` object.

The supplied 2016 journal version has now been compared with the thesis:
see [KIAZYK_2016_REVIEW.md](KIAZYK_2016_REVIEW.md). Its Section 2 is the
preferred proof reference; this review does not change the proved scope.

## Read this theorem first

[UniversalStarEmbedding.lean](SixVertexUnfolding/Geometry/UniversalStarEmbedding.lean)
proves `universal_star_embedding`. Its inputs are six original vertices,
triangular or quadrilateral original faces, and an original source adjacent
to every other vertex. Its conclusion is a continuous open embedding of the
actual surface outside the five star cuts into the plane, with bounded,
path-connected image, finite straight-segment boundary, and exact local
intrinsic distance preservation. The tree, charts, angle bounds, and
separation are constructed, not supplied as assumptions.

[UniversalStarUnfolding.lean](SixVertexUnfolding/Geometry/UniversalStarUnfolding.lean)
then applies the existing whole-face conversion. Its short final corollary,
`hasEdgeUnfolding_of_universal_vertex`, uses the earlier small-solid and
large-face reductions to cover **every convex polyhedron with at most six
vertices having a universal vertex**, with no separate face-size assumption.
The main theorem's proof script now closes this branch. Its sole remaining
`sorry` is confined to the prism-with-diagonal branch.

The earlier [CofacialStarEmbedding.lean](SixVertexUnfolding/Geometry/CofacialStarEmbedding.lean)
remains the corresponding result for the four canonical nonuniversal graph
models with a cofacial original source. The cofacial hypothesis is impossible
for the all-triangular octahedron; no such source is asserted there.

## Earlier canonical construction

1. The actual shortest-path cut locus is a finite tree. Cofacial original
   targets are its leaves; internal junctions have flat surface charts.
2. [GlobalKiteSeparation](SixVertexUnfolding/Geometry/GlobalKiteSeparation.lean)
   develops every kite in one common plane and separates distinct kites
   using the actual source-cone budget along their connecting tree path.
3. [StarOpenEmbedding](SixVertexUnfolding/Geometry/StarOpenEmbedding.lean)
   assembles the complete triangle maps and constructs inverse disks at
   every retained point. [StarLocalMetric](SixVertexUnfolding/Geometry/StarLocalMetric.lean)
   proves exact local intrinsic isometry.
4. [RetainedCutConnectivity](SixVertexUnfolding/Geometry/RetainedCutConnectivity.lean)
   joins retained rays through the cut tree after its original leaves are
   removed, proving connectivity of the actual retained surface.
5. [StarPolygonBoundary](SixVertexUnfolding/Geometry/StarPolygonBoundary.lean)
   identifies the entire planar boundary with explicit finite cut segments.
   [StarPolygonClosure](SixVertexUnfolding/Geometry/StarPolygonClosure.lean)
   identifies the closure with the finite closed-kite union.

These five bounded construction milestones are complete in the stated
scope. Their completion is not an overall proof percentage.

## Transfer to whole original faces

[StarEdgeAssembly](SixVertexUnfolding/Geometry/StarEdgeAssembly.lean) is a
proved generic conversion for any convex polyhedron. From an injective
continuous local intrinsic isometry, retained-surface connectivity, and
cuts avoiding all original face interiors, it constructs every field of
`EdgeUnfolding`: whole-face rigid placements, nonoverlap, an original hinge
spanning tree, and agreement along each complete hinge.

[UniversalStarInteriors](SixVertexUnfolding/Geometry/UniversalStarInteriors.lean)
proves the face-interior condition for a universal source. The actual
universal-source development and its application to this conversion are now proved in `UniversalStarUnfolding`.

## Universal-vertex geometry: checked angle deficit, detours, and avoidance

- [UniversalVertexCycle](SixVertexUnfolding/Geometry/UniversalVertexCycle.lean)
  constructs the actual five-cycle around a universal vertex. Every link
  vertex has exactly two neighbors, supplied by its two incident faces.
- [UniversalVertexFigure](SixVertexUnfolding/Geometry/UniversalVertexFigure.lean)
  constructs all five transverse rays and their supporting sides from actual
  original faces. Every nonincident ray lies strictly below the relevant
  supporting side. The five chosen faces are distinct and exhaust all incident faces.
- [UniversalVertexNeighborhood](SixVertexUnfolding/Geometry/UniversalVertexNeighborhood.lean)
  proves these five triangles cover the whole surface near the vertex,
  and transverse normalization preserves the actual spatial angles.
- [FiveRayPerimeter](SixVertexUnfolding/Geometry/FiveRayPerimeter.lean)
  proves that every supported five-ray figure has total sector angle
  strictly below `2 * Real.pi`. Its enclosing triangle and both corner
  cuts are constructed, not assumed.
- [UniversalVertexCurvature](SixVertexUnfolding/Geometry/UniversalVertexCurvature.lean)
  transfers this strict bound to the actual five original incident faces.
- [FiveFaceFanDetours](SixVertexUnfolding/Geometry/FiveFaceFanDetours.lean)
  develops the actual five faces, folds short planar chords back to surface
  paths, and chooses the slit using the strict angle bound. A single open
  neighborhood admits a strict detour between any two nonpole surface points.
- [UniversalVertexAvoidance](SixVertexUnfolding/Geometry/UniversalVertexAvoidance.lean)
  proves that simple finite shortest paths cannot pass through the universal
  vertex. Constant-speed shortest paths between distinct endpoints satisfy
  this automatically. The fan, angle deficit, and detours are constructed
  from the polyhedron; they are not extra premises of these theorems.

The polyhedron results assume six vertices and triangular or quadrilateral
faces. The abstract five-ray bound has no graph-family hypothesis.
The five-face detour and avoidance milestones are complete. The newer
construction below extends avoidance to every vertex of the solid.

## All vertices: local geometry without a canonical graph

[SmallPolyhedronVertexAvoidance](SixVertexUnfolding/Geometry/SmallPolyhedronVertexAvoidance.lean)
proves strict local detours at every original vertex, and vertex-free
interiors for every simple finite shortest route. Constant-speed shortest
paths between distinct endpoints satisfy this automatically, and such
finite simple paths exist.

The hypotheses are just at most six vertices and triangular or quadrilateral
faces. No universal vertex, cofacial source, or canonical graph is assumed.
The source and target may be arbitrary surface points.

- `FacetCornerNeighbors` and `VertexNeighborLink` identify the two incident
  faces on each edge and construct one cyclic link through all edge neighbors.
- `VertexFaceFan` lists actual corner triangles. `FacetCornerNeighborhood`
  proves that these cover the whole surface locally, including quadrilateral
  faces. `VertexFanIncidence` proves every incident face occurs exactly once.
- `VertexFanFigure` constructs the actual supporting rays. `VertexFanAngles`
  proves the full surface angle is below two pi in all three possible degrees.
- `VertexFanCoordinates` through `VertexFanAvoidance` develop and fold the
  corner triangles, choose the short angular route, and exclude the vertex
  by a strict improvement in length. All geometric inputs are constructed.

[SmallPolyhedronShortestRoutes](SixVertexUnfolding/Geometry/SmallPolyhedronShortestRoutes.lean)
already applies this to finite normalized geodesic fibers, finite developed
distance formulas, source images, and nonbranching of shortest routes.
`SmallPolyhedronLocalDistance` and `SmallPolyhedronSourceUniqueness` prove
local distance formulas and route uniqueness away from source-image ties.
[SmallPolyhedronCutCover](SixVertexUnfolding/Geometry/SmallPolyhedronCutCover.lean)
gives a finite straight-segment cover of the entire actual cut set,
including points on original edges and original vertices.

The cover theorem alone is only containment. The following construction
now proves the exact segment decomposition and tree structure.

## Actual cut tree without a canonical graph

[SmallPolyhedronCutTree](SixVertexUnfolding/Geometry/SmallPolyhedronCutTree.lean)
proves `small_exists_regular_cut_tree`: the actual `P.CutLocusTree a` exists
assuming only at most six vertices and triangular/quadrilateral faces.
The source `a` is any surface point. Neither a universal vertex nor a
cofacial-source hypothesis is required for this tree result.

1. `SmallPolyhedronRouteStability` proves local route-count stability,
   closedness of the augmented cut set, and compactness.
2. The `SmallPolyhedronFace*` and `SmallPolyhedronEdge*` modules prove exact
   local Voronoi descriptions using actual shortest-route sources and real
   competing paths. `SmallPolyhedronCutSegments` uses finite distance
   crossings and compactness to obtain an exact finite segment union and
   an embedded graph, with arbitrary finite cut-point markings.
3. `SmallPolyhedronRoutePrefixes`, `SmallPolyhedronRayExtensions`, and
   `SmallPolyhedronTerminalRays` prove unique proper prefixes, strict
   extension at noncut points, and terminality at cut points.
   `SmallPolyhedronCutRetraction` constructs the continuous retraction of
   the punctured surface to the cut set and proves the latter contractible.
   The existing generic embedded-graph theorems then give connectedness
   and acyclicity.
4. `SmallPolyhedronJunctions` proves global junction finiteness.
   Every junction and original cut vertex is marked in the constructed
   tree. `small_cut_tree_open_edge_two_routes` proves exactly two actual
   shortest routes at each point inside an open tree edge.

The construction uses the existing geometric definitions; it does not
assume tree structure or replace the actual cut set with a covering graph.
The radial triangle construction, surface coverage, and original-vertex
leaf property have now been transferred as described below. A full
leaf-if-and-only-if-original theorem in this broader scope is not claimed.

## Actual radial triangles and cofacial charts: proved

[SmallPolyhedronCutEdgeTriangles](SixVertexUnfolding/Geometry/SmallPolyhedronCutEdgeTriangles.lean)
constructs both closed radial triangle developments along every actual
cut-tree edge, with their surface homeomorphisms. The continuous route
families, injectivity, disjointness, metric models, and folded triangle
maps are proved from the broader shortest-route results.

[SmallPolyhedronCutTreeTriangleCoverage](SixVertexUnfolding/Geometry/SmallPolyhedronCutTreeTriangleCoverage.lean)
proves these triangles cover the whole surface. These two constructions
allow any surface source on a polyhedron with at most six vertices and
triangular/quadrilateral faces.

For a source sharing a face with every vertex,
[SmallPolyhedronUniqueRouteLeaves](SixVertexUnfolding/Geometry/SmallPolyhedronUniqueRouteLeaves.lean)
proves each original cut-tree vertex is a leaf. The actual nonvertex
junction fans and consistent frames then assemble into `CutTreeCharts` in
[SmallPolyhedronCutTreeCharts](SixVertexUnfolding/Geometry/SmallPolyhedronCutTreeCharts.lean).
Its short `small_exists_universal_star_charts` theorem constructs both the
tree and the charts from a universal source. Coverage, flat junction
compatibility, original leaves, and reverse-edge frames are all proved.
Global kite separation and injectivity of the assembled retained-surface
map are now proved as described below.

## Local angle accounting without a canonical graph: proved

[VertexFanSectorIntersections](SixVertexUnfolding/Geometry/VertexFanSectorIntersections.lean)
uses actual supporting sides to identify every sector intersection.
[VertexFanCircle](SixVertexUnfolding/Geometry/VertexFanCircle.lean) joins
their angle coordinates modulo the actual total fan angle, including
the closing seam, and proves continuity on the punctured fan.

The circle metric comparison, complete small-circle coverage, folded
triangle corner arcs, and incident-triangle neighborhood coverage give
[VertexFanCutTreeConeCoverage](SixVertexUnfolding/Geometry/VertexFanCutTreeConeCoverage.lean):
the sum of incident triangle corners is at least the original vertex's
actual surface angle. This holds for every original cut vertex and any
surface source in the small-polyhedron scope, independently of the chosen
metric models. No numerical cone-coverage inequality is assumed.

[SmallPolyhedronJunctionAngleSum](SixVertexUnfolding/Geometry/SmallPolyhedronJunctionAngleSum.lean)
also proves that the corners around a flat cut-tree junction sum to exactly
two pi. These are the two local inputs for the global angle budget.

## Universal-source global angle budget and kite separation: proved

[UniversalVertexFaceCounting](SixVertexUnfolding/Geometry/UniversalVertexFaceCounting.lean)
proves the needed face count directly. Five triangular faces meet the source,
and at least two distinct faces exclude it. If there are `t` triangles and
`q` quadrilaterals, edge double-counting gives `3t + 4q = 2E`, hence `t` is
even. Together with `t ≥ 5` and `t + q ≥ 7`, this gives `t + 2q ≥ 8`.

[FacetCornerAngles](SixVertexUnfolding/Geometry/FacetCornerAngles.lean)
defines each actual corner angle using its two original face edges, and
proves independence of their ordering. `QuadrilateralCornerAngles` splits
angles along a crossing diagonal. `FacetAngleSums` then proves the ordinary
angle sums of π and 2π for triangular and quadrilateral original faces.

[SmallPolyhedronCurvature](SixVertexUnfolding/Geometry/SmallPolyhedronCurvature.lean)
identifies every actual fan sum with the angles of all incident faces.
Summing by faces gives total face angle at least 8π, hence total vertex
curvature at most 4π. **This upper bound is sufficient**; a general Euler
formula or the exact global curvature identity is unnecessary here.

`SmallPolyhedronCutTreeCurvature` transfers each original curvature to the
cut tree exactly once, omitting the source. The checked local cone and flat
junction inequalities and the tree angle identity then yield
[SmallPolyhedronSourceBudget](SixVertexUnfolding/Geometry/SmallPolyhedronSourceBudget.lean):

```text
sum of directed source angles ≤ actual surface angle at the source < 2π;
half the directed sum < π.
```

[UniversalStarKiteSeparation](SixVertexUnfolding/Geometry/UniversalStarKiteSeparation.lean)
applies that budget to every simple chain in the fixed global frames.
`universal_global_kites_nonoverlap` proves that one kite is disjoint from the
interior of every different tree-edge kite. `universal_exists_separated_cut_tree_charts`
constructs the actual covering charts with this property. These results
assume six vertices, triangular/quadrilateral faces, and a universal source;
no canonical graph, numerical angle inequality, or nonoverlap premise is supplied.

## Retained-surface assembly: proved

1. `SmallPolyhedronStarCutEndpoints` identifies the star cuts with rays
   ending at original vertices. The `SmallPolyhedron*MapAgreement` modules
   prove full agreement of overlapping triangle maps, including edge
   reversal and junction rays. `SmallPolyhedronStarDevelopmentContinuity`
   glues the finite closed cover continuously.
2. `SmallPolyhedronStarInverseDisks` constructs actual inverse disks in
   triangle interiors, cut-edge bases, retained endpoint rays, and flat
   junctions. `SmallPolyhedronStarOpenEmbedding` proves global injectivity
   and openness; `SmallPolyhedronStarLocalMetric` proves exact local
   intrinsic isometry.
3. `SmallPolyhedronRetainedCutConnectivity` joins retained rays through
   the cut tree after its original leaves are removed.
   `SmallPolyhedronStarPolygonBoundary` identifies the entire planar
   boundary with the finite union of actual straight cut-side segments.
4. `UniversalStarEmbedding` supplies the proved chart separation from the
   actual universal-source angle budget and packages the complete result.
   `UniversalStarUnfolding` keeps every original face whole and derives an
   original-edge hinge tree and nonoverlap in the public definition.

The intermediate inverse-map results explicitly assume
`CutTreeCharts.KitesSeparated`. This is a geometric property, not an axiom:
`UniversalStarKiteSeparation` proves it from the original solid, and the
final universal theorem discharges that input. The broader gluing and
connectivity results need only at most six vertices, small faces, and a
cofacial source; they do not assume a canonical graph.

Bounded progress for the universal-source star milestone: angle budget,
global kite separation, gluing/inverse maps, local metric, connectivity,
and polygonal boundary are **6/6 complete (100%)**. Its conversion to a
whole-face edge unfolding is also complete. This percentage refers to this
specified star case, not to the full six-vertex theorem or the general paper.

## Remaining scope

The fully arbitrary-source star theorem still requires internal
original-vertex junctions; the current cofacial construction does not
claim to handle these. Arbitrary vertex counts and general geodesic-curve
sources from the paper are also outside this completed milestone.

For the main six-vertex edge-unfolding theorem, the universal-vertex branch
is now closed. The single unfinished target branch is the prism with a
diagonal outside its already proved regions. No new proof of that separate
branch was attempted in this star-only checkpoint.

## Validation

The latest full checkpoint checks 992 Lean files and audits 4,544 project
theorem declarations using only `propext`, `Classical.choice`, and
`Quot.sound`. Later checkpoints are recorded in [WORKLOG.md](WORKLOG.md).
The sole original main-theorem `sorry` remains in `Statement.lean`;
no proved library module introduces a new proof hole or axiom.
