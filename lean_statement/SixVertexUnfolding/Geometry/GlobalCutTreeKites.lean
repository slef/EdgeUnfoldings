import SixVertexUnfolding.Geometry.CutTreeCharts

/-! The paired triangle images are well defined in the chosen global
plane, independently of which orientation names their cut-tree edge. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace RadialStripTriangle

/-- Agreement of full surface maps identifies the entire planar triangle image. -/
theorem AgreesAfter.image_triangle {P : ConvexPolyhedron}
    {routes other : C(unitInterval, P.BoundaryCurve)} {p l r q u v : Plane}
    {D : RadialStripTriangle routes p l r} {E : RadialStripTriangle other q u v}
    {motion : Plane ≃ᵃⁱ[ℝ] Plane} (agrees : D.AgreesAfter E motion) :
    motion '' convexHull ℝ ({p, l, r} : Set Plane) = convexHull ℝ ({q, u, v} : Set Plane) := by
  have included {routes other : C(unitInterval, P.BoundaryCurve)} {p l r q u v : Plane}
      {D : RadialStripTriangle routes p l r} {E : RadialStripTriangle other q u v}
      {motion : Plane ≃ᵃⁱ[ℝ] Plane} (agrees : D.AgreesAfter E motion) :
      motion '' convexHull ℝ ({p, l, r} : Set Plane) ⊆ convexHull ℝ ({q, u, v} : Set Plane) := by
    rintro _ ⟨x, hx, rfl⟩
    let b := D.homeomorph.symm ⟨x, hx⟩
    have other_member : b.val ∈ range (closedRouteStripMap other) := agrees.1 ▸ b.property
    have same := agrees.2 b.val b.property other_member
    change motion (D.homeomorph (D.homeomorph.symm ⟨x, hx⟩)) =
      (E.homeomorph ⟨b.val, other_member⟩ : Plane) at same
    rw [D.homeomorph.apply_symm_apply] at same
    exact same.symm ▸ (E.homeomorph ⟨b.val, other_member⟩).property
  apply Subset.antisymm (included agrees)
  intro y hy
  exact ⟨motion.symm y, included agrees.symm ⟨y, hy, rfl⟩, motion.apply_symm_apply y⟩

end RadialStripTriangle

namespace PlacedCutEdgeTriangles

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v w z : T.vertices} {edge : T.graph.Adj u v} {other : T.graph.Adj w z}

/-- The union of the two actual placed triangles of a cut edge. -/
def kite (D : PlacedCutEdgeTriangles T edge) : Set Plane :=
  convexHull ℝ ({D.motion D.model.first, D.motion D.model.left, D.motion D.model.right} : Set Plane) ∪
  convexHull ℝ ({D.motion D.model.second, D.motion D.model.left, D.motion D.model.right} : Set Plane)

theorem AgreesAfter.image_kite {D : PlacedCutEdgeTriangles T edge} {E : PlacedCutEdgeTriangles T other}
    {transition : Plane ≃ᵃⁱ[ℝ] Plane} (agrees : D.AgreesAfter E transition) :
    transition '' D.kite = E.kite := by
  rw [kite, image_union]
  rcases agrees with same | swapped
  · rw [same.1.image_triangle, same.2.image_triangle]
    rfl
  · rw [swapped.1.image_triangle, swapped.2.image_triangle, union_comm]
    rfl

/-- Changing the coordinate frame moves the complete paired image by that one motion. -/
theorem kite_inFrame (D : PlacedCutEdgeTriangles T edge) (frame : Plane ≃ᵃⁱ[ℝ] Plane) :
    (D.inFrame frame).kite = frame '' D.kite := by
  have triangle (p l r : Plane) : frame '' convexHull ℝ ({p, l, r} : Set Plane) =
      convexHull ℝ ({frame p, frame l, frame r} : Set Plane) := by
    change frame.toAffineMap '' convexHull ℝ ({p, l, r} : Set Plane) = _
    rw [frame.toAffineMap.image_convexHull]
    simp only [image_insert_eq, image_singleton]
    rfl
  simp only [kite, image_union, triangle]
  rfl

end PlacedCutEdgeTriangles

namespace CutTreeCharts

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)

/-- The actual kite in the one global plane chosen for the whole tree. -/
noncomputable def kite {u v : T.vertices} (edge : T.graph.Adj u v) : Set Plane :=
  ((charts.triangles edge).inFrame (charts.frames.frame u)).kite

theorem kite_reverse {u v : T.vertices} (edge : T.graph.Adj u v) :
    charts.kite edge = charts.kite edge.symm := by
  have same := (charts.frames.global_reversal edge).2.2.image_kite
  simpa only [AffineIsometryEquiv.coe_refl, image_id] using same

/-- At a nonvertex junction the global kite is exactly the image of its fixed fan kite. -/
theorem kite_at_fan {u v : T.vertices} (edge : T.graph.Adj u v) (nonvertex : (u : Space) ∉ P.vertices) :
    charts.kite edge = charts.frames.frame u ''
      ((charts.fan u nonvertex).edgeTriangles edge).developedKite := by
  unfold kite
  rw [PlacedCutEdgeTriangles.kite_inFrame, charts.at_fan edge nonvertex]
  rfl

include charts in
/-- Every actual internal passage has a flat chart in this fixed collection. -/
theorem internal_nonvertex {u v w : T.vertices} (first : T.graph.Adj u v) (second : T.graph.Adj u w)
    (different : v ≠ w) : (u : Space) ∉ P.vertices := by
  intro original
  obtain ⟨q, _, only⟩ := charts.original_leaves u original
  exact different ((only v first).trans (only w second).symm)

/-- The chosen global edge transition swaps the actual roots of the two fixed fans. -/
theorem transition_at_fans {u v : T.vertices} (edge : T.graph.Adj u v)
    (nonvertex_u : (u : Space) ∉ P.vertices) (nonvertex_v : (v : Space) ∉ P.vertices) :
    let first := charts.fan u nonvertex_u
    let second := charts.fan v nonvertex_v
    charts.frames.transition edge first.order.chart.origin = second.order.chart.origin +
      dist (v : Space) (u : Space) • direction (second.edgeIndex edge.symm) ∧
    charts.frames.transition edge (first.order.chart.origin +
      dist (u : Space) (v : Space) • direction (first.edgeIndex edge)) = second.order.chart.origin := by
  have same := charts.frames.reverses edge
  rw [charts.at_fan edge nonvertex_u, charts.at_fan edge.symm nonvertex_v] at same
  let D := (charts.fan u nonvertex_u).edgeTriangles edge
  let E := (charts.fan v nonvertex_v).edgeTriangles edge.symm
  have left : charts.frames.transition edge (D.motion D.model.left) = E.motion E.model.right := same.1
  have right : charts.frames.transition edge (D.motion D.model.right) = E.motion E.model.left := same.2.1
  rw [D.at_junction, E.at_neighbor] at left
  rw [D.at_neighbor, E.at_junction] at right
  exact ⟨left, right⟩

end CutTreeCharts
end SixVertexUnfolding.ConvexPolyhedron
