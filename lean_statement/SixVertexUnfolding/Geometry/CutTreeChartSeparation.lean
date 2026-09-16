import SixVertexUnfolding.Geometry.GlobalCutTreeKites

/-! The geometric separation property used to assemble an injective star map.
It is proved for universal sources in `UniversalStarKiteSeparation`; the
gluing and inverse-chart arguments can use the property independently. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutTreeCharts

open Set

/-- Distinct tree-edge kites do not meet each other's interiors. -/
def KitesSeparated {P : ConvexPolyhedron} {a : frontier P.body}
    {T : P.CutLocusTree a} (charts : CutTreeCharts T) : Prop :=
  ∀ {u v w z : T.vertices} (first : T.graph.Adj u v) (last : T.graph.Adj w z),
    s(u, v) ≠ s(w, z) → Disjoint (charts.kite first) (interior (charts.kite last))

end SixVertexUnfolding.ConvexPolyhedron.CutTreeCharts
