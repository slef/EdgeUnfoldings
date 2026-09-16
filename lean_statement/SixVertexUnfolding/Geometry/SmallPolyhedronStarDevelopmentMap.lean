import SixVertexUnfolding.Geometry.StarDevelopmentMap
import SixVertexUnfolding.Geometry.SmallPolyhedronGlobalMapAgreement

/-! Assemble the actual triangle maps into one function on the
surface outside the star cuts. Its values there are independent of
every triangle, side and edge-orientation choice.
This version uses at most six vertices and triangular/quadrilateral faces,
without a canonical graph assumption. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

/-- Every original triangle map agrees with the assembled development wherever it is uncut. -/
theorem small_develop_agrees {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v : T.vertices} (edge : T.graph.Adj u v) {b : frontier P.body} {x : Plane}
    (outside : b ∉ P.starCuts a) (placed : (charts.global edge).Places b x) : charts.develop b = x := by
  obtain ⟨w, z, other, selected⟩ := charts.develop_spec b
  exact small_global_triangle_placements_agree size small_faces charts cofacial other edge outside selected placed

/-- In particular, the restriction to each triangle is its full proved surface homeomorphism. -/
theorem small_develop_on_triangle {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v : T.vertices} (edge : T.graph.Adj u v) (side : Bool) (b : frontier P.body)
    (inside : b ∈ range (closedRouteStripMap ((charts.global edge).routes side)))
    (outside : b ∉ P.starCuts a) :
    charts.develop b = ((charts.global edge).sideTriangle side).homeomorph ⟨b, inside⟩ :=
  small_develop_agrees size small_faces charts cofacial edge outside ⟨side, inside, rfl⟩

end SixVertexUnfolding.ConvexPolyhedron
