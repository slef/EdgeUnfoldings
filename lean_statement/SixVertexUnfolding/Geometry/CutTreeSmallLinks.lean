import SixVertexUnfolding.Geometry.CutTreeVertexStrips
import SixVertexUnfolding.Geometry.RadialStripCornerGeometry

/-! A sufficiently small sphere about a cut-tree vertex is covered by
the folded circular sections of its actual incident triangles. Planar
and spatial radii agree exactly, also at an original cone vertex. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutEdgeTriangles

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
  {u v : T.vertices} {edge : T.graph.Adj u v} (D : CutEdgeTriangles T edge)

/-- Both developments preserve radius from their common actual base endpoint locally. -/
theorem left_radial_radius : ∃ ε > 0,
    (∀ b : range (closedRouteStripMap D.first), dist (b.val : Space) (u : Space) < ε →
      dist (D.first_triangle.homeomorph b : Plane) D.model.left = dist (b.val : Space) (u : Space)) ∧
    (∀ b : range (closedRouteStripMap D.second), dist (b.val : Space) (u : Space) < ε →
      dist (D.second_triangle.homeomorph b : Plane) D.model.left = dist (b.val : Space) (u : Space)) := by
  have first_target : D.first 0 1 = T.vertexTarget u :=
    (congrArg Prod.snd (D.member 0).1.2).trans (T.closedEdgeTarget_zero edge)
  have second_target : D.second 0 1 = T.vertexTarget u :=
    (congrArg Prod.snd (D.member 0).2.2).trans (T.closedEdgeTarget_zero edge)
  obtain ⟨ε, positive, first⟩ := D.first_triangle.left_radial_distance
  obtain ⟨δ, dp, second⟩ := D.second_triangle.left_radial_distance
  rw [first_target] at first
  rw [second_target] at second
  exact ⟨min ε δ, lt_min positive dp,
    fun b near => first b (near.trans_le (min_le_left _ _)),
    fun b near => second b (near.trans_le (min_le_right _ _))⟩

end CutEdgeTriangles

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Every point of a small actual vertex link comes from a circular
section with the same radius in one outgoing incident triangle. -/
theorem incident_triangles_cover_small_links (a : frontier P.body) (T : P.CutLocusTree a)
    (triangles : (d : T.graph.Dart) → CutEdgeTriangles T d.adj) (u : T.vertices) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε, ∀ b : frontier P.body, dist (b : Space) (u : Space) = ρ →
      ∃ v : T.vertices, ∃ edge : T.graph.Adj u v,
        let D := triangles ⟨(u, v), edge⟩
        (∃ z : convexHull ℝ ({D.model.first, D.model.left, D.model.right} : Set Plane),
          dist (z : Plane) D.model.left = ρ ∧ (D.first_triangle.homeomorph.symm z).val = b) ∨
        (∃ z : convexHull ℝ ({D.model.second, D.model.left, D.model.right} : Set Plane),
          dist (z : Plane) D.model.left = ρ ∧ (D.second_triangle.homeomorph.symm z).val = b) := by
  classical
  letI : Fintype T.vertices := T.finite_vertices.fintype
  choose radius positive radial using (fun d : T.graph.Dart => (triangles d).left_radial_radius)
  obtain ⟨U, openU, center, covered⟩ := graph.incident_triangles_cover_neighborhood small_faces a T triangles u
  let V : Set (frontier P.body) := U ∩ ⋂ d : T.graph.Dart, Metric.ball (T.vertexTarget u) (radius d)
  have openV : IsOpen V := openU.inter (isOpen_iInter_of_finite (fun d => Metric.isOpen_ball))
  have centerV : T.vertexTarget u ∈ V :=
    ⟨center, mem_iInter.mpr (fun d => Metric.mem_ball_self (positive d))⟩
  obtain ⟨ε, ep, inside⟩ := Metric.isOpen_iff.mp openV (T.vertexTarget u) centerV
  refine ⟨ε, ep, ?_⟩
  intro ρ hr b sphere
  have near : b ∈ V := inside (by change dist (b : Space) (u : Space) < ε; rw [sphere]; exact hr.2)
  obtain ⟨v, edge, belongs⟩ := covered b near.1
  let d : T.graph.Dart := ⟨(u, v), edge⟩
  have short : dist (b : Space) (u : Space) < radius d := mem_iInter.mp near.2 d
  refine ⟨v, edge, ?_⟩
  rcases belongs with first | second
  · left
    refine ⟨(triangles d).first_triangle.homeomorph ⟨b, first⟩, ?_, ?_⟩
    · exact ((radial d).1 ⟨b, first⟩ short).trans sphere
    · exact congrArg Subtype.val ((triangles d).first_triangle.homeomorph.symm_apply_apply ⟨b, first⟩)
  · right
    refine ⟨(triangles d).second_triangle.homeomorph ⟨b, second⟩, ?_, ?_⟩
    · exact ((radial d).2 ⟨b, second⟩ short).trans sphere
    · exact congrArg Subtype.val ((triangles d).second_triangle.homeomorph.symm_apply_apply ⟨b, second⟩)

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
