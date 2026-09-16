# Checked shortest-path foundations

Any two points on the actual polyhedral boundary admit a finite shortest
surface route. Its length is Mathlib total variation, and shortestness compares
with every continuous boundary path, including infinite-length paths. For
distinct endpoints a shortest route can be chosen injective, with constant
arc speed. It has a finite subdivision into straight portions in original
whole facets. These results hold without a six-vertex restriction.

The public 55-line definition layer and 15-line theorem file are unchanged.
This machinery belongs entirely to the internal proof library.

| Module | Checked result and role |
| --- | --- |
| [ArcLength](SixVertexUnfolding/Geometry/ArcLength.lean) | The existing path length equals variation directly on the unit interval. Accumulated length is continuous and covers the complete interval from zero to total length. Unit-speed curves are 1-Lipschitz. |
| [SurfaceReparameterization](SixVertexUnfolding/Geometry/SurfaceReparameterization.lean) | Every finite-length surface path has a replacement with speed bounded by its length, the same endpoints and image, and no greater length. Zero length and pauses are included. |
| [SurfacePathJoining](SixVertexUnfolding/Geometry/SurfacePathJoining.lean) | Joining paths adds their lengths. Connected facet walks give a finite-length path between any boundary endpoints. |
| [SurfacePathCompactness](SixVertexUnfolding/Geometry/SurfacePathCompactness.lean) | Fixed endpoints, the closed compact boundary, and a common speed bound define a compact family. Total variation is lower semicontinuous and attains a minimum there. |
| [ShortestSurfacePaths](SixVertexUnfolding/Geometry/ShortestSurfacePaths.lean) | The compact-family minimizer is shortest among all continuous surface paths. A shorter competitor could be reparameterized into the same compact family. |
| [ShortestSubpaths](SixVertexUnfolding/Geometry/ShortestSubpaths.lean) | Replacing a shorter portion would shorten the whole path. Thus shortest cofacial portions follow their chord; a face cannot be left and revisited. |
| [ShortestFaceSubdivision](SixVertexUnfolding/Geometry/ShortestFaceSubdivision.lean) | Each visited face occupies a closed entry-to-exit interval. Their finitely many endpoints partition the route into straight, chord-length portions in whole facets. |
| [ShortestSimplePaths](SixVertexUnfolding/Geometry/ShortestSimplePaths.lean) | A speed bound equal to total length forces exact constant arc speed. A repeated point would give a positive-duration shortest loop of zero length, so a chosen shortest route with distinct endpoints is injective. |

The finite subdivision is recorded as a finite set of parameter times
containing zero and one. For each consecutive pair, the theorem provides a
whole facet containing the entire portion, straight-segment containment,
and equality of the portion length with the endpoint distance. This permits
pauses and visits confined to face boundaries.

Local straight continuation, flat metric charts, and local nonbranching are
now proved; see [LOCAL_GEODESICS.md](LOCAL_GEODESICS.md). No star nonoverlap
theorem is assumed or proved here. Intermediate vertices are now excluded
for all four canonical six-vertex models, though not yet for arbitrary
polyhedra or the universal-vertex family. The finite developments, source
copies, route stability, and unique-route contraction are mapped in
[CUT_LOCUS_FOUNDATIONS.md](CUT_LOCUS_FOUNDATIONS.md). The cut-locus tree,
kite partition, and planar separation remain to be built.
See [STAR_NEXT.md](STAR_NEXT.md) for the remaining main-theorem dependencies.
