import SixVertexUnfolding.Geometry.FacetHalfspaces
import SixVertexUnfolding.Geometry.Edges

/-!
At an original vertex, the incident facet normals span three-space. Otherwise a
small segment tangent to all incident facets would pass through that vertex and
remain inside the solid, contradicting extremality.
-/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Incident facet normals span the ambient space at every genuine vertex. -/
theorem incident_normals_span (P : ConvexPolyhedron)
    (normal : P.Face → Space) (level : P.Face → ℝ)
    (face_eq : ∀ F, F.val = {x ∈ P.body | inner ℝ (normal F) x = level F})
    (body_eq : P.body = {x | ∀ F, inner ℝ (normal F) x ≤ level F})
    {v : Space} (vertex : v ∈ P.vertices) :
    Submodule.span ℝ (normal '' {F | v ∈ F.val}) = ⊤ := by
  classical
  let N := Submodule.span ℝ (normal '' {F | v ∈ F.val})
  by_contra not_full
  have orthogonal_nontrivial : Nᗮ ≠ ⊥ := by
    intro zero
    exact not_full (Submodule.orthogonal_eq_bot_iff.mp zero)
  obtain ⟨q, q_orthogonal, q_nonzero⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot orthogonal_nontrivial
  have v_in := P.vertices_subset_body vertex
  have v_bounds : ∀ F, inner ℝ (normal F) v ≤ level F := by
    rw [body_eq] at v_in
    exact v_in

  -- All nonincident inequalities stay strict for sufficiently small motion.
  let inactive := {F : P.Face // v ∉ F.val}
  let times : Set ℝ := ⋂ F : inactive,
    {t | inner ℝ (normal F.val) (v + t • q) < level F.val}
  have open_times : IsOpen times := by
    apply isOpen_iInter_of_finite
    intro F
    exact isOpen_lt (by fun_prop) continuous_const
  have zero_in : (0 : ℝ) ∈ times := by
    apply Set.mem_iInter.mpr
    intro F
    simp only [zero_smul, add_zero, Set.mem_setOf_eq]
    apply lt_of_le_of_ne (v_bounds F.val)
    intro equal_height
    exact F.property ((face_eq F.val).symm ▸ ⟨v_in, equal_height⟩)
  obtain ⟨radius, radius_pos, nearby⟩ := Metric.isOpen_iff.mp open_times 0 zero_in
  let step := radius / 2
  have step_pos : 0 < step := half_pos radius_pos
  have forward_time : step ∈ times := by
    apply nearby
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos step_pos]
    dsimp [step]
    linarith
  have backward_time : -step ∈ times := by
    apply nearby
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos step_pos]
    dsimp [step]
    linarith

  -- Incident inequalities remain equalities because the motion is tangent to them.
  have stays_in {t : ℝ} (small : t ∈ times) : v + t • q ∈ P.body := by
    rw [body_eq]
    intro F
    by_cases incident : v ∈ F.val
    · have normal_in : normal F ∈ N := Submodule.subset_span ⟨F, incident, rfl⟩
      have perpendicular := N.inner_right_of_mem_orthogonal normal_in q_orthogonal
      simpa only [inner_add_right, inner_smul_right, perpendicular, mul_zero, add_zero]
        using v_bounds F
    · exact (Set.mem_iInter.mp small ⟨F, incident⟩).le
  have left_in := stays_in forward_time
  have right_in : v - step • q ∈ P.body := by
    simpa only [neg_smul, ← sub_eq_add_neg] using stays_in backward_time
  have between : v ∈ segment ℝ (v + step • q) (v - step • q) := by
    simpa only [midpoint_add_sub] using
      midpoint_mem_segment (𝕜 := ℝ) (v + step • q) (v - step • q)
  have shifted_nonzero : step • q ≠ 0 := smul_ne_zero step_pos.ne' q_nonzero
  rcases P.vertex_in_segment_is_endpoint vertex left_in right_in between with left | right
  · exact shifted_nonzero (add_left_cancel (left.trans (add_zero v).symm))
  · exact shifted_nonzero (sub_eq_self.mp right)

/-- Every original vertex belongs to at least three different facets. -/
theorem three_le_incident_facet_count (P : ConvexPolyhedron) {v : Space}
    (vertex : v ∈ P.vertices) : 3 ≤ Nat.card {F : P.Face // v ∈ F.val} := by
  classical
  letI : Fintype ({F : P.Face | v ∈ F.val} : Set P.Face) := Fintype.ofFinite _
  obtain ⟨normal, level, _, face_eq, body_eq⟩ := P.exists_facet_halfspace_representation
  have spanning := P.incident_normals_span normal level face_eq body_eq vertex
  rw [Set.image_eq_range] at spanning
  have dimension_bound := finrank_le_of_span_eq_top spanning
  change 3 ≤ Nat.card ({F : P.Face | v ∈ F.val} : Set P.Face)
  rw [Nat.card_eq_fintype_card]
  simpa [Space] using dimension_bound

end SixVertexUnfolding.ConvexPolyhedron
