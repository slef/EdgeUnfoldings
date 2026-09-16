# The checked source-angle budget

The source-angle budget is now proved both in the canonical graph scope
and for six-vertex polyhedra with a universal source and triangular or
quadrilateral faces. See [STAR_NEXT.md](STAR_NEXT.md) for the current
checkpoint. The full universal-source star embedding remains unfinished.

The universal-source extension uses `SmallPolyhedronSourceBudget`.
Original face angles are summed directly; the face count gives total
curvature at most 4π, which suffices for the budget. The local cone bounds
and flat junction sums come from the broader actual chart construction.
`UniversalStarKiteSeparation` applies this to all kites in the common plane.

The older canonical implementation is mapped below.

The argument has four concrete parts.

1. The closed radial triangles cover the whole actual boundary. Near a
   tree vertex only its incident triangles are needed. Their finite rigid
   folding pieces preserve distance from that vertex locally. Thus the
   triangles' circular sections cover its small spatial link with exactly
   the same radius. See
   [CutTreeSmallLinks.lean](SixVertexUnfolding/Geometry/CutTreeSmallLinks.lean).
2. The four original triangular sectors carry one continuous angular
   coordinate modulo the actual cone angle. Their shared radial edges
   agree, including the closing seam and a flat subdivision corner.
   Every direction occurs on every sufficiently small link. See
   [OctahedralFanCircle.lean](SixVertexUnfolding/Geometry/OctahedralFanCircle.lean)
   and [OctahedralFanCircleCoverage.lean](SixVertexUnfolding/Geometry/OctahedralFanCircleCoverage.lean).
3. Each small triangle corner arc maps to that angular circle without
   increasing parameter distances. Within one original sector, ordinary
   angles compare by the chord inequality and equal radii. A finite closed
   cover extends this bound along the entire arc; no finite-crossing
   assumption is made. See
   [FoldedCornerCircleLength.lean](SixVertexUnfolding/Geometry/FoldedCornerCircleLength.lean).
   A nonexpanding interval image lies in the circle ball centered at its
   midpoint image with half its interval length as radius. Mathlib's circle
   measure formula and finite subadditivity then give the coverage inequality
   in [CircleCoverLength.lean](SixVertexUnfolding/Geometry/CircleCoverLength.lean).
4. [CutTreeConeCoverage.lean](SixVertexUnfolding/Geometry/CutTreeConeCoverage.lean)
   combines these actual constructions. At every original tree vertex,
   the sum of incident triangle corners is at least its actual cone angle,
   independently of the chosen planar metric models. The flat-vertex sums,
   edge-reversal identities, tree count, and total curvature then yield
   [CutTreeSourceBudget.lean](SixVertexUnfolding/Geometry/CutTreeSourceBudget.lean):

   ```text
   sum of directed source angles ≤ cone angle at the source
   half that directed sum < π.
   ```

[CutTreePathBudget.lean](SixVertexUnfolding/Geometry/CutTreePathBudget.lean)
proves the same strict π bound for every simple path: a path never uses
both orientations of an edge, and every source angle is positive. Its
accumulated outer angle therefore lies in `[π/2, 3π/2)`.

The modules in the list above use the four canonical `SixVertexGraph`
models. The broader vertex-avoidance, cone-coverage, and universal-source
budget results are recorded in the current checkpoint linked above.
No global unfolding conclusion is assumed in the argument.
