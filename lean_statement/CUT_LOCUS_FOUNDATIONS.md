# Checked foundations for the cut-locus argument

The main unfolding theorem remains unfinished. The results below construct
shortest routes and study their developments and topology directly on the
actual convex polyhedral boundary. The public definitions and theorem
statement remain unchanged. No star-unfolding theorem is assumed.

The general metric results apply to every public `ConvexPolyhedron`.
Results needing exclusion of intermediate vertices currently apply to the
four canonical six-vertex graph models, with triangular or quadrilateral
original facets. That exclusion remains missing for the universal-vertex
family. The more general versions display vertex avoidance as a premise.

| Step | Checked result | Main modules |
| --- | --- | --- |
| Bounded face itinerary | Each normalized shortest route has at most `2 * Nat.card P.Face + 1` straight face portions. Consecutive faces agree or share an original edge when interior vertices are avoided. | [ShortestFaceItinerary](SixVertexUnfolding/Geometry/ShortestFaceItinerary.lean) |
| One coherent development | Outward placements are joined along all successive hinges. In this single development the route is one affine segment, and its endpoint distance equals its full intrinsic length. | [FaceChainDevelopment](SixVertexUnfolding/Geometry/FaceChainDevelopment.lean), [ShortestDevelopedLine](SixVertexUnfolding/Geometry/ShortestDevelopedLine.lean) |
| Fixed finite source copies | Each bounded face sequence has one chosen development, independent of the route and endpoints. A coordinate change puts its source copy in the target face's fixed coordinates. | [FiniteFaceSequences](SixVertexUnfolding/Geometry/FiniteFaceSequences.lean), [FiniteSourceImages](SixVertexUnfolding/Geometry/FiniteSourceImages.lean) |
| Finite actual routes | A terminal source code determines the entire normalized route by nonbranching. Thus there are finitely many actual shortest routes, including routes ending at original vertices. | [TerminalSourceImage](SixVertexUnfolding/Geometry/TerminalSourceImage.lean), [FinitelyManyShortestRoutes](SixVertexUnfolding/Geometry/FinitelyManyShortestRoutes.lean) |
| Finite line cover | At a target belonging to one original face, multiple shortest routes force equal distances to two distinct source copies. Such targets lie in finitely many explicit straight bisectors and are nowhere dense in that face's plane. | [SourceImageUniqueness](SixVertexUnfolding/Geometry/SourceImageUniqueness.lean), [MultipleShortestRoutes](SixVertexUnfolding/Geometry/MultipleShortestRoutes.lean), [SourceBisectorDensity](SixVertexUnfolding/Geometry/SourceBisectorDensity.lean) |
| Compact route family | All normalized geodesics, even with both endpoints varying, form a compact set in the uniform metric. These are exactly genuine shortest surface paths. An open neighborhood of an endpoint pair's routes contains every route for sufficiently nearby endpoint pairs. | [GeodesicCurveCompactness](SixVertexUnfolding/Geometry/GeodesicCurveCompactness.lean), [GeodesicCurvePaths](SixVertexUnfolding/Geometry/GeodesicCurvePaths.lean), [GeodesicEndpointStability](SixVertexUnfolding/Geometry/GeodesicEndpointStability.lean) |
| No local splitting | A source copy can be recovered continuously from the endpoint and any earlier route point in the target face. Its finite set isolates each route. For a fixed source, nearby routes with equal targets agree. | [TerminalSourceRecovery](SixVertexUnfolding/Geometry/TerminalSourceRecovery.lean), [GeodesicSourceRecovery](SixVertexUnfolding/Geometry/GeodesicSourceRecovery.lean), [GeodesicBranchIsolation](SixVertexUnfolding/Geometry/GeodesicBranchIsolation.lean) |
| Target neighborhoods | At a distinct target belonging to one face, uniqueness persists nearby and the number of shortest routes cannot increase nearby. The multiple-route locus is relatively closed away from the source and face edges. | [UniqueGeodesicNeighborhoods](SixVertexUnfolding/Geometry/UniqueGeodesicNeighborhoods.lean), [GeodesicBranchCount](SixVertexUnfolding/Geometry/GeodesicBranchCount.lean), [MultipleRouteTopology](SixVertexUnfolding/Geometry/MultipleRouteTopology.lean) |
| Unique-route contraction | Unique routes depend continuously on endpoints in the uniform metric. Every prefix is unique. Consequently the complete unique-route target set contracts to the source along these routes. This result holds for every public convex polyhedron. | [ContinuousUniqueRoutes](SixVertexUnfolding/Geometry/ContinuousUniqueRoutes.lean), [UniqueGeodesicPrefixes](SixVertexUnfolding/Geometry/UniqueGeodesicPrefixes.lean), [UniqueTargetContraction](SixVertexUnfolding/Geometry/UniqueTargetContraction.lean) |
| Proper prefixes and global density | In the canonical models, every proper prefix of any shortest route is unique, even when the final endpoint has several routes. Such a route cannot pass through a multiple-route target before its end. Unique-route targets are dense in the entire boundary, including near edges and vertices. | [ShortestExtensionUniqueness](SixVertexUnfolding/Geometry/ShortestExtensionUniqueness.lean), [UniqueRouteDensity](SixVertexUnfolding/Geometry/UniqueRouteDensity.lean) |
| Actual local minimum | Each actual terminal source supplies real surface competitors to all nearby targets in its face. Compactness supplies the converse selection. Intrinsic distance is exactly the minimum over the finite, nonempty set of sources of the original target's actual routes. | [TerminalSourceCompetitors](SixVertexUnfolding/Geometry/TerminalSourceCompetitors.lean), [ActiveSources](SixVertexUnfolding/Geometry/ActiveSources.lean), [LocalMinimumDistance](SixVertexUnfolding/Geometry/LocalMinimumDistance.lean) |
| Exact face diagram | The multiple-route locus is locally exactly the nearest-source Voronoi boundary. The sources count actual routes bijectively. Two routes give a full local bisector, and only finitely many interior-face targets have three or more routes. | [ActiveSourceRoutes](SixVertexUnfolding/Geometry/ActiveSourceRoutes.lean), [LocalVoronoiCutLocus](SixVertexUnfolding/Geometry/LocalVoronoiCutLocus.lean), [FaceCutLocusStructure](SixVertexUnfolding/Geometry/FaceCutLocusStructure.lean) |
| Edge source recovery | Both incident faces' finite source lists are placed in the same joined coordinates. Recovery from an earlier visit to a metric neighborhood gives the actual terminal source, even for targets and routes on the shared edge. Its continuity prevents local splitting. | [EdgeSourceImages](SixVertexUnfolding/Geometry/EdgeSourceImages.lean), [EdgeTerminalRecovery](SixVertexUnfolding/Geometry/EdgeTerminalRecovery.lean), [EdgeBranchIsolation](SixVertexUnfolding/Geometry/EdgeBranchIsolation.lean) |
| Stability across edges | Route counts cannot increase nearby, uniqueness persists, and the multiple-route locus is relatively closed throughout the nonvertex boundary, across original edges as well as face interiors. | [NonvertexRouteStability](SixVertexUnfolding/Geometry/NonvertexRouteStability.lean) |
| Exact edge diagram | Each actual terminal source supplies exact-length surface competitors on both sides of an original edge. Distance is locally their finite minimum, and multiple routes are exactly the nearest-source ties in the joined coordinates. | [EdgeTerminalCompetitors](SixVertexUnfolding/Geometry/EdgeTerminalCompetitors.lean), [EdgeLocalMinimum](SixVertexUnfolding/Geometry/EdgeLocalMinimum.lean), [EdgeLocalVoronoi](SixVertexUnfolding/Geometry/EdgeLocalVoronoi.lean) |
| Global finite junctions | One fixed joined development and finite source list work along each entire original edge. Together with the face results and finite original vertex set, this proves global finiteness of targets with at least three shortest routes. | [EdgeJunctions](SixVertexUnfolding/Geometry/EdgeJunctions.lean), [FiniteJunctions](SixVertexUnfolding/Geometry/FiniteJunctions.lean) |
| Regular cut arcs | Outside the finite set of junctions and original vertices, every cut point has exactly two routes and a flat chart of its full straight cut line. An actual interval through it preserves intrinsic distance and covers all nearby multiple-route points. | [RegularCutPoints](SixVertexUnfolding/Geometry/RegularCutPoints.lean), [CutLineCharts](SixVertexUnfolding/Geometry/CutLineCharts.lean), [CutLineArcs](SixVertexUnfolding/Geometry/CutLineArcs.lean), [CutArcTopology](SixVertexUnfolding/Geometry/CutArcTopology.lean) |
| Source neighborhood | For every public polyhedron, cofacial routes are unique. Every source has a neighborhood of such targets, so multiple-route points cannot accumulate at the source. | [SourceNeighborhood](SixVertexUnfolding/Geometry/SourceNeighborhood.lean) |
| Compact cut set | The explicitly defined set of multiple-route targets and original vertices other than the source is compact in canonical models. Its complement contracts to the source along actual shortest routes. | [ClosedCutSet](SixVertexUnfolding/Geometry/ClosedCutSet.lean), [CutSetContraction](SixVertexUnfolding/Geometry/CutSetContraction.lean) |
| Finite line crossings | On a straight line, two source distances either agree everywhere or tie at at most one parameter. Away from the finitely many crossings, membership in the actual cut set persists along a cofacial segment. | [LineSourceCrossings](SixVertexUnfolding/Geometry/LineSourceCrossings.lean), [SegmentCutCrossings](SixVertexUnfolding/Geometry/SegmentCutCrossings.lean) |
| Exact finite segments | The cut set meets each cofacial segment in finitely many closed intervals, including endpoints. A finite cover by clipped source bisectors and original skeleton segments then gives an exact global finite union of cofacial closed segments. | [CompactRealIntervals](SixVertexUnfolding/Geometry/CompactRealIntervals.lean), [SegmentCutPieces](SixVertexUnfolding/Geometry/SegmentCutPieces.lean), [FiniteCutSegments](SixVertexUnfolding/Geometry/FiniteCutSegments.lean) |
| Finite embedded graph | Splitting at all endpoints and crossings gives a finite graph with exactly the cut set as its trace. No vertex lies inside an edge; intersecting open edges have the same unordered endpoints. All edges remain in whole original facets. | [SegmentArrangementGraph](SixVertexUnfolding/Geometry/SegmentArrangementGraph.lean), [SegmentGraphEmbedding](SixVertexUnfolding/Geometry/SegmentGraphEmbedding.lean), [EmbeddedCutGraph](SixVertexUnfolding/Geometry/EmbeddedCutGraph.lean) |
| Local graph topology | The actual cut set is a continuous quotient of finitely many compact intervals. It is locally path connected and has finitely many connected and path components, including at original vertices and junctions. | [CutSetIntervalQuotient](SixVertexUnfolding/Geometry/CutSetIntervalQuotient.lean) |
| Farthest shortest extensions | Equality in the intrinsic triangle inequality defines a compact set of possible endpoints. A farthest endpoint exists and is realized by a genuine normalized shortest route through the prescribed point. | [ShortestRayEndpoints](SixVertexUnfolding/Geometry/ShortestRayEndpoints.lean), [ShortestExtensionPaths](SixVertexUnfolding/Geometry/ShortestExtensionPaths.lean) |
| Terminal cut points | A local single-source formula permits strict continuation in both face interiors and edge charts. Every farthest ray ends in the cut set, and a shortest route cannot continue through a cut point. | [NoncutRayExtension](SixVertexUnfolding/Geometry/NoncutRayExtension.lean), [MaximalRaysReachCutSet](SixVertexUnfolding/Geometry/MaximalRaysReachCutSet.lean), [CutSetTerminalRays](SixVertexUnfolding/Geometry/CutSetTerminalRays.lean) |
| Unique continuous endpoint | Equal-speed rays from one source cannot meet and branch even when their endpoints differ. Rescaling proves a unique terminal cut endpoint through every nonsource point. The endpoint map is continuous and fixes cut points. | [SameSourceGeodesics](SixVertexUnfolding/Geometry/SameSourceGeodesics.lean), [UniqueCutEndpoint](SixVertexUnfolding/Geometry/UniqueCutEndpoint.lean), [CutEndpointRetraction](SixVertexUnfolding/Geometry/CutEndpointRetraction.lean) |
| Connected cut graph | The endpoint retraction makes the cut set path connected. Closed geometric component traces transfer this conclusion to every exact finite embedded cut graph. | [CutSetConnected](SixVertexUnfolding/Geometry/CutSetConnected.lean), [EmbeddedGraphComponents](SixVertexUnfolding/Geometry/EmbeddedGraphComponents.lean), [ConnectedCutGraph](SixVertexUnfolding/Geometry/ConnectedCutGraph.lean) |
| Contractible cut set | The punctured boundary is homeomorphic to the plane. Composing its contraction with inclusion and the endpoint retraction contracts the cut set itself, including its spatial trace. | [PuncturedBoundaryContraction](SixVertexUnfolding/Geometry/PuncturedBoundaryContraction.lean), [CutSetContractible](SixVertexUnfolding/Geometry/CutSetContractible.lean) |
| Original vertex limits | The cut set has at least two original vertices and is connected, so it has no isolated points. Removing its finite original-vertex subset leaves a dense set of actual multiple-route targets. The cut set equals exactly their closure. | [CutSetVertexLimits](SixVertexUnfolding/Geometry/CutSetVertexLimits.lean) |

For the unique-route contraction, `uniqueTargets P a` is simply the set of boundary
targets having a unique normalized shortest route from `a`. The actual
homotopy is proved continuous and stays in that set. Its endpoints are the
constant map at `a` and the identity. `MultipleRouteTopology` identifies
this set with the complement of `multipleRouteLocus`.

Several distinctions matter for the unfinished proof:

- The original finite source list contains candidates. Distance is now
  proved to be a local minimum over the **actual active sources** at a fixed
  nonvertex target, including original edge interiors. It is not asserted to be the minimum over every
  face-sequence candidate.
- The exact local Voronoi diagram uses those active sources. Equality with
  the entire union of candidate bisectors is not claimed. The actual compact
  cut set is now proved to be exactly a finite union of selected closed
  segment pieces, with a checked embedded graph subdivision.
- `multipleRouteLocus` means exactly targets with two distinct shortest
  routes. The explicit `cutSet` adds the original vertices other than the
  source. In the canonical models it is now proved to be exactly the closure
  of the multiple-route locus and exactly the terminal shortest-ray points.
- The cut graph is connected and its actual trace is contractible. The
  formal implication to graph acyclicity is now proved: the real lift of
  an edge's circle map detects that edge as a bridge. All leaves are
  original vertices. No geodesic triangle partition or kite separation is assumed.

The remaining route to the manuscript's star theorem is to align the
constructed radial triangles globally, prove the kite-chain angle and
separation argument, and transfer the resulting placements to whole original facets. The
universal-vertex case also needs vertex avoidance beyond the four canonical
models. The prism-with-diagonal fallback and switches remain separate
obligations. [STAR_NEXT.md](STAR_NEXT.md) records those exact gaps.

The finite embedded tree and its original-vertex leaves are now checked.
The acyclicity proof uses Mathlib's homotopy lifting for the covering from
the real line to the circle. For leaves, finite active sources give a
Voronoi boundary with at least two points on each small circle around a
junction. A one-sided cofacial segment cannot contain two distinct points
at the same intrinsic distance from its endpoint.

The radial surface partition is now checked in
[CutTreeRadialPartition](SixVertexUnfolding/Geometry/CutTreeRadialPartition.lean).
The actual route family over a regular target family is a two-sheet covering;
lifting along the open edge gives two globally continuous branches. Their
swept strips are injectively parametrized and mutually disjoint. A point's
unique terminal endpoint identifies its strip or one of the finitely many
tree-vertex rays.

Compactness and finite endpoint fibers force each branch to have a unique
limit at both tree vertices. A continuous curve cannot oscillate between
finitely many possible limits: a separating distance sphere would force an
additional cluster point. This constructs continuous closed-edge families.
Their closed images are exactly the closures of the open strips.

Connectedness fixes each branch's actual terminal source copy, in either
face coordinates or joined hinge coordinates. The two copies are distinct
and equidistant from both edge endpoints. They form nondegenerate metric
triangles, on strictly opposite sides of their common base. All radial
distances agree with intrinsic source distances, including at the endpoints.

[CutStripTriangleTopology](SixVertexUnfolding/Geometry/CutStripTriangleTopology.lean)
proves the closed strip and its metric triangle are homeomorphic. Both are
continuous images of the compact radial square, collapsing exactly the
zero-time side to the source. The induced homeomorphism respects the radial
parameters. It preserves distances along each individual shortest ray.
The actual coordinate map now preserves distances on convex patches of
original faces and on flat-chart patches crossing original hinges. Along
each shortest route the developed point is selected from finitely many
rigid original-face placements. A continuous finite selection of maps with
a common Lipschitz bound retains that bound on a convex region. This proves
that the inverse triangle map is nonexpanding; applying the same argument
in surface flat charts proves exact local distance preservation.

Every open strip is open in the actual boundary. Its triangle coordinates
identify it exactly with the ordinary triangle interior. At every strip
point, including an original hinge interior, the map agrees on a flat disk
with one rigid planar motion and maps that disk onto a planar disk. Both
triangle developments for each cut-tree edge are constructed using the
actual chosen route branches and the same metric kite.

[CutTreeTrianglePairs](SixVertexUnfolding/Geometry/CutTreeTrianglePairs.lean)
checks the join of two successive actual strips sharing a route to their
common tree vertex. Their intrinsic-distance profiles give equal radial
lengths, and a planar motion aligns the complete route. Reflection chooses
the outward side, so the two triangles meet exactly along that ray.
Distinct closed cut edges meet only at common endpoints; shortest-ray
uniqueness then shows that the two surface strips overlap exactly along
the same route. Their maps paste into a single homeomorphism of the unions.
Moving a triangle preserves all its previously proved metric guarantees.
The two source angles of each metric kite are equal and strictly between
zero and pi; their global cumulative bound is not yet established.

This joins two pieces. Global coherence around junctions, the cumulative
source-angle bound, distant-kite separation, and transfer to whole original
facets remain open. Intermediate-vertex avoidance for the universal-vertex
family also remains outside the canonical-model results.
