# Five-ray angle deficit and local detour: proved

Checkpoint: 16 September 2026, 07:26 UTC. The five-ray work is complete and its
detour argument has now been extended to all small-face vertices.

The formerly missing bound is now a checked Lean theorem in
[FiveRayPerimeter.lean](SixVertexUnfolding/Geometry/FiveRayPerimeter.lean):

```lean
theorem sum_angles_lt_two_pi (fan : FiveRayFan) :
    ∑ i : Fin 5, angle (fan.ray i) (fan.ray (i + 1)) < 2 * Real.pi
```

Its only input is the existing supported five-ray figure. No enclosing
triangle, corner ordering, or angle bound is added as an assumption.

## The checked construction

1. `FiveRayCoordinates` proves that three consecutive rays form a basis.
   Supporting heights determine the signs of the other corners'
   coefficients. The same construction works after every cyclic relabelling.
2. `FiveRaySupportChoice` proves that if a side direction fails to approach
   the supporting line two sides ahead, the direction two places later
   does approach its opposite line. A five-cycle cannot alternate forever,
   so two suitable directions exist. A coefficient identity translates
   the second advance into the required opposite-neighbor inequality.
3. `FiveRayEnclosure` extends the two sides of the chosen corner to the
   opposite supporting line. If that line is parametrized with the original
   middle vertices at 0 and 1, the new outer corners have parameters below
   0 and above 1. This proves all four segment incidences required by the
   two-corner-cut theorem.
4. `FiveRayPerimeter` applies the existing spherical triangle bound and
   the two corner-cut inequalities, then removes the cyclic relabelling.

## Transfer to the polyhedron

[UniversalVertexCurvature.lean](SixVertexUnfolding/Geometry/UniversalVertexCurvature.lean)
constructs the supported figure from the actual polyhedron and transfers
its bound back to the spatial angles of the original incident edges.
Its witnesses retain the cyclic order and the five original triangular
faces, together with their exhaustion of all incident faces.

The polyhedron corollary has the same hypotheses as the existing
`UniversalVertexFigure` construction: six vertices, triangular or
quadrilateral faces, and a source adjacent to every other vertex.
The abstract five-ray theorem has no graph-family hypothesis.

## Checked local detour and vertex avoidance

[FiveFaceFan.lean](SixVertexUnfolding/Geometry/FiveFaceFan.lean) packages
the actual five faces, with a proved constructor from the polyhedron.
The development uses their original lengths and angles. Adjacent planar
triangles meet only on their shared radial segment; separated triangles
meet only at the pole. Their rigid inverses therefore paste to a finite
surface folding.

A sufficiently small planar chord whose angular width is below pi stays
inside the developed fan and folds to a strictly shorter surface path.
The two angular routes between any two nonpole points add to the total
angle, which is below two pi. Choosing the appropriate slit therefore
always produces such a chord. Taking the minimum of the five slit radii
gives a uniform neighborhood on the actual surface.

[UniversalVertexAvoidance.lean](SixVertexUnfolding/Geometry/UniversalVertexAvoidance.lean)
uses this strict shortcut to rule out the universal vertex at any interior
time of a simple finite shortest path. It also proves avoidance for
constant-speed shortest paths and existence of such finite simple routes.
No fan, detour, or angle-bound hypothesis is left for the caller.

These particular results retain the six-vertex, triangular/quadrilateral-face,
universal-vertex hypotheses above. The subsequent
[SmallPolyhedronVertexAvoidance.lean](SixVertexUnfolding/Geometry/SmallPolyhedronVertexAvoidance.lean)
now proves avoidance of every original vertex for any polyhedron with at
most six vertices and triangular or quadrilateral faces. Its actual local
cycles, corner-triangle neighborhoods, and angle bounds are constructed
without a canonical graph premise. The source may be any surface point.

## Next proof obligation

The degree-three/four local geometry and all-vertex avoidance are complete.
`SmallPolyhedronShortestRoutes` applies them to finite normalized geodesic
fibers, finite developments, source images, and nonbranching.
`SmallPolyhedronCutTree` now constructs the exact finite cut tree for this
larger family, with all junctions and original cut vertices marked. The
cut set is compact and contractible, and every open tree edge has exactly
two shortest routes. Transfer of radial-triangle and cofacial-leaf
constructions to these broader inputs remains. Circle
coordinates for the new fans and global curvature/source-angle accounting
also remain. The precise integration boundary is in `STAR_NEXT.md`.

The full star theorem remains unfinished. The surface-angle milestone
and the local detour/avoidance milestone at every vertex are each 100%
complete in the stated small-face scope; the subsequent global integration
is not. The finite-route and exact cut-tree milestones are also complete.

Full validation: 892 Lean files, 4,292 audited project theorem declarations,
standard axioms only. Public definitions and statement remain unchanged.
