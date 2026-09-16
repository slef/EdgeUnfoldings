# Checked local geometry of shortest routes

Every nonvertex boundary point now has a genuine planar chart preserving the
surface's shortest-path distance. The chart and inverse are continuous in the
existing Euclidean subspace topology. Constant-speed shortest routes are
affine lines in these coordinates.

Two shortest routes with the same endpoints that meet at a nonvertex
interior point agree in a neighborhood of that point. If a route's entire
interior avoids original vertices, this agreement propagates to the whole
route. Vertex avoidance is now proved for all four canonical six-vertex
graph models, so their global nonbranching results have no avoidance premise.
It remains unproved for arbitrary polyhedra and the universal-vertex family.
No star nonoverlap theorem follows yet.

| Proof group | Main checked statements |
| --- | --- |
| [ShortestHingeVariation](SixVertexUnfolding/Geometry/ShortestHingeVariation.lean), [ShortestHingeStraightness](SixVertexUnfolding/Geometry/ShortestHingeStraightness.lean) | Varying the crossing point along an original edge gives a stationary length. Outward placement of its two facets turns this into straight continuation. Both placements are constructed. |
| [NonvertexFacetNeighborhoods](SixVertexUnfolding/Geometry/NonvertexFacetNeighborhoods.lean), [LocalFacetHalfspaces](SixVertexUnfolding/Geometry/LocalFacetHalfspaces.lean) | A nonvertex point belongs to one or two facets. Nearby, all other supporting inequalities stay strict. A single facet is locally its whole plane; an edge gives two actual half-planes. |
| [FacetPlaneInverse](SixVertexUnfolding/Geometry/FacetPlaneInverse.lean), [EdgeFolding](SixVertexUnfolding/Geometry/EdgeFolding.lean), [EdgeFlatNeighborhood](SixVertexUnfolding/Geometry/EdgeFlatNeighborhood.lean) | Every rigid facet placement has an affine inverse on its plane. The two inverses glue continuously, have no identifications on the relevant halves, and cover an actual boundary neighborhood. |
| [EdgeSegmentPaths](SixVertexUnfolding/Geometry/EdgeSegmentPaths.lean), [EdgeLocalMetric](SixVertexUnfolding/Geometry/EdgeLocalMetric.lean) | A planar segment lifts with exactly its length. A short minimizing route cannot escape a sufficiently small two-facet neighborhood. Its intrinsic distance is therefore exactly the planar distance. |
| [SurfaceDistance](SixVertexUnfolding/Geometry/SurfaceDistance.lean), [IntrinsicSurfaceMetric](SixVertexUnfolding/Geometry/IntrinsicSurfaceMetric.lean) | Intrinsic distance is finite, attained, symmetric, and satisfies the metric axioms. Its topology is the original boundary topology, which is compact. Constant-speed minimizing routes realize the geodesic distance formula. |
| [SurfaceFlatCharts](SixVertexUnfolding/Geometry/SurfaceFlatCharts.lean), [FlatChartCoordinates](SixVertexUnfolding/Geometry/FlatChartCoordinates.lean), [ShortestFlatCoordinates](SixVertexUnfolding/Geometry/ShortestFlatCoordinates.lean) | Every nonvertex boundary point has a flat metric chart and continuous inverse. A shortest route contained in it is exactly an affine interpolation of its endpoints. |
| [ShortestLocalNonbranching](SixVertexUnfolding/Geometry/ShortestLocalNonbranching.lean), [ShortestNonbranching](SixVertexUnfolding/Geometry/ShortestNonbranching.lean) | Common endpoints and an interior meeting force local agreement away from vertices. With vertex avoidance, connectedness propagates equality globally; distinct routes then have disjoint open traces. |
| [FiniteSurfaceFolding](SixVertexUnfolding/Geometry/FiniteSurfaceFolding.lean), [OctahedralFanFolding](SixVertexUnfolding/Geometry/OctahedralFanFolding.lean), [OctahedralVertexDetours](SixVertexUnfolding/Geometry/OctahedralVertexDetours.lean) | Finite rigid pieces fold planar chords without increasing length. The actual four-triangle fans admit small chords, and complementary slit choices use positive curvature to give a strict detour around each vertex. |
| [OctahedralVertexAvoidance](SixVertexUnfolding/Geometry/OctahedralVertexAvoidance.lean), [OctahedralShortestNonbranching](SixVertexUnfolding/Geometry/OctahedralShortestNonbranching.lean) | Simple shortest routes in all four canonical graph models avoid intermediate vertices. Distinct constant-speed shortest routes with common endpoints have disjoint open traces. |

All these constructions use the actual convex hull, whole supporting facets,
and continuous surface paths from the public definitions. They introduce no
abstract surface axiom. The 55-line public definitions and 15-line target
theorem file remain unchanged.

The next missing star ingredients are vertex avoidance beyond the four canonical models,
the cut-locus tree and kite partition, planar kite-chain separation, and
transfer to whole original facets. Bounded developments, finite source
copies, finite route families, endpoint stability, and a contraction of the
unique-route target set are now also checked; see
[CUT_LOCUS_FOUNDATIONS.md](CUT_LOCUS_FOUNDATIONS.md). See
[STAR_NEXT.md](STAR_NEXT.md) for the outstanding main-theorem dependencies.
