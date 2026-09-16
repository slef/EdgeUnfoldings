# Star unfolding: current proved result and next gap

Checkpoint: 16 September 2026, 15:49 UTC. The full star theorem is unfinished.
The public definitions and theorem statement are unchanged.

The actual cut tree, its radial triangles, and local cone-angle coverage
are now proved without a canonical graph assumption. For a cofacial source,
including a universal vertex, the complete chart collection is constructed.
The broader global source-angle budget and star embedding remain unfinished.

The supplied 2016 journal version has now been compared with the thesis:
see [KIAZYK_2016_REVIEW.md](KIAZYK_2016_REVIEW.md). Its Section 2 is the
preferred proof reference; this review does not change the proved scope.

## Read this theorem first

[CofacialStarEmbedding.lean](SixVertexUnfolding/Geometry/CofacialStarEmbedding.lean)
constructs a continuous open embedding of the actual surface outside the
specified star cuts into the plane. Its image is bounded and path connected,
its boundary is a finite union of closed straight segments, and the map
preserves the local intrinsic distance.

Its hypotheses matter: it uses `SixVertexGraph`, triangular or quadrilateral
faces, and a source vertex sharing a face with every original vertex.
`SixVertexGraph` comprises the four nonuniversal canonical graph models.
This does not cover universal-vertex solids or arbitrary sources. The
cofacial-source condition is impossible for the all-triangular octahedron;
this theorem is not a claim that all four models have such a source.

## Checked construction

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
universal-source planar development is still missing; the conversion
must not be mistaken for that construction.

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
compatibility, original leaves, and reverse-edge frames are all proved;
global injectivity is a separate remaining step.

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

## Next proof obligation

The remaining angle step is **global curvature accounting**. Identify the
sum of actual fan angles over all original vertices and prove the total
curvature is four pi. The existing `OctahedralAngles.sum_curvature` uses a
fixed eight-triangle subdivision of a canonical six-vertex graph; it does
not yet establish that identity for the universal-vertex family.

Once that identity is available, combine the checked local cone inequalities,
flat full-turn identities, and tree angle accounting to bound all directed
source angles by the source's actual surface angle. Its strict bound below
two pi is already proved. Then transfer the existing global kite separation
and retained-surface gluing to the broader chart construction.

For a fully arbitrary-source star theorem, internal original-vertex
junctions also remain to be handled. They are unnecessary for the current
cofacial/universal-source milestone. The full theorem is still unfinished.

## Validation

The latest full checkpoint checks 947 Lean files and audits 4,422 project
theorem declarations using only `propext`, `Classical.choice`, and
`Quot.sound`. Later checkpoints are recorded in [WORKLOG.md](WORKLOG.md).
The sole original main-theorem `sorry` remains in `Statement.lean`;
no proved library module introduces a new proof hole or axiom.
