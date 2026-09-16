import SixVertexUnfolding.Geometry.VertexFacets
import SixVertexUnfolding.Geometry.EdgeGraph

/-! No original vertex can belong to every facet of a bounded convex solid. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Every original vertex is excluded by at least one whole facet. -/
theorem exists_facet_excluding_vertex (P : ConvexPolyhedron) (v : P.Vertex) :
    ∃ F : P.Face, (v : Space) ∉ F.val := by
  by_contra all_incident
  push Not at all_incident
  obtain ⟨w, vertex, different⟩ := P.vertices.exists_mem_ne
    (by have := P.four_le_vertex_count; omega) (v : Space)
  obtain ⟨normal, level, _, face_eq, body_eq⟩ := P.exists_facet_halfspace_representation
  have spanning := P.incident_normals_span normal level face_eq body_eq vertex
  have vanishes : Set.EqOn (innerSL ℝ ((v : Space) - w)).toLinearMap
      (0 : Space →ₗ[ℝ] ℝ) (normal '' {F | w ∈ F.val}) := by
    rintro _ ⟨F, wF, rfl⟩
    change w ∈ F.val at wF
    have at_v : inner ℝ (normal F) v = level F := ((face_eq F) ▸ all_incident F).2
    have at_w : inner ℝ (normal F) w = level F := ((face_eq F) ▸ wF).2
    change inner ℝ ((v : Space) - w) (normal F) = 0
    rw [real_inner_comm, inner_sub_right, at_v, at_w, sub_self]
  have everywhere := LinearMap.eqOn_span vanishes
  rw [spanning] at everywhere
  have zero := everywhere (show (v : Space) - w ∈ (⊤ : Submodule ℝ Space) from trivial)
  change inner ℝ ((v : Space) - w) ((v : Space) - w) = 0 at zero
  exact different (sub_eq_zero.mp (inner_self_eq_zero.mp zero)).symm

end SixVertexUnfolding.ConvexPolyhedron
