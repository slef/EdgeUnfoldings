import SixVertexUnfolding.Geometry.GlobalMapAgreement

/-! Assemble the actual triangle maps into one function on the
surface outside the star cuts. Its values there are independent of
every triangle, side and edge-orientation choice. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutTreeCharts

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)

theorem exists_developed_point (b : frontier P.body) :
    ∃ x : Plane, ∃ u v : T.vertices, ∃ edge : T.graph.Adj u v, (charts.global edge).Places b x := by
  obtain ⟨u, v, edge, x, placed⟩ := charts.exists_global_placement b
  exact ⟨x, u, v, edge, placed⟩

/-- A selected triangle value; values on cut rays themselves are not used for gluing. -/
noncomputable def develop (b : frontier P.body) : Plane := (charts.exists_developed_point b).choose

theorem develop_spec (b : frontier P.body) :
    ∃ u v : T.vertices, ∃ edge : T.graph.Adj u v, (charts.global edge).Places b (charts.develop b) :=
  (charts.exists_developed_point b).choose_spec

end CutTreeCharts

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

/-- Every original triangle map agrees with the assembled development wherever it is uncut. -/
theorem develop_agrees {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v : T.vertices} (edge : T.graph.Adj u v) {b : frontier P.body} {x : Plane}
    (outside : b ∉ P.starCuts a) (placed : (charts.global edge).Places b x) : charts.develop b = x := by
  obtain ⟨w, z, other, selected⟩ := charts.develop_spec b
  exact graph.global_triangle_placements_agree small_faces charts cofacial other edge outside selected placed

/-- In particular, the restriction to each triangle is its full proved surface homeomorphism. -/
theorem develop_on_triangle {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v : T.vertices} (edge : T.graph.Adj u v) (side : Bool) (b : frontier P.body)
    (inside : b ∈ range (closedRouteStripMap ((charts.global edge).routes side)))
    (outside : b ∉ P.starCuts a) :
    charts.develop b = ((charts.global edge).sideTriangle side).homeomorph ⟨b, inside⟩ :=
  graph.develop_agrees small_faces charts cofacial edge outside ⟨side, inside, rfl⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
