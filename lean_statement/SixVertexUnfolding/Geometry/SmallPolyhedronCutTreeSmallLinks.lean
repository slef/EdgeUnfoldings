import SixVertexUnfolding.Geometry.CutTreeSmallLinks
import SixVertexUnfolding.Geometry.SmallPolyhedronCutTreeVertexStrips

/-! A sufficiently small sphere about a cut-tree vertex is covered by
the folded circular sections of its actual incident triangles. Planar
and spatial radii agree exactly, also at an original cone vertex.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Every point of a small actual vertex link comes from a circular
section with the same radius in one outgoing incident triangle. -/
theorem small_incident_triangles_cover_small_links (a : frontier P.body) (T : P.CutLocusTree a)
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
  obtain ⟨U, openU, center, covered⟩ := small_incident_triangles_cover_neighborhood size small_faces a T triangles u
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

end SixVertexUnfolding.ConvexPolyhedron
