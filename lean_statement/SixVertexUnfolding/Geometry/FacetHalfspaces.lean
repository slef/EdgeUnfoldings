import SixVertexUnfolding.Geometry.BoundaryCoverage

/-! The finite family of facet halfspaces recovers the entire convex solid. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- A segment from an interior point to an exterior point exits through the boundary before its end. -/
theorem segment_exit (P : ConvexPolyhedron) {a z : Space}
    (inside : a ∈ interior P.body) (outside : z ∉ P.body) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ AffineMap.lineMap a z t ∈ frontier P.body := by
  let line := AffineMap.lineMap (k := ℝ) a z
  let times : Set ℝ := Set.Icc 0 1 ∩ line ⁻¹' P.body
  have line_continuous : Continuous line := AffineMap.lineMap_continuous
  have compact_times : IsCompact times :=
    isCompact_Icc.inter_right (P.body_closed.preimage line_continuous)
  have time_zero : (0 : ℝ) ∈ times := by
    exact ⟨⟨le_rfl, zero_le_one⟩, by simpa [line] using interior_subset inside⟩
  obtain ⟨t, ht, last⟩ := compact_times.exists_isGreatest ⟨0, time_zero⟩
  have before_end : t < 1 := lt_of_le_of_ne ht.1.2 (by
    intro at_end
    have end_inside := ht.2
    rw [at_end] at end_inside
    exact outside (by simpa [line] using end_inside))
  refine ⟨t, ht.1.1, before_end, subset_closure ht.2, ?_⟩
  intro still_inside
  have nearby : ∀ᶠ u in nhds t, line u ∈ interior P.body ∧ u < 1 :=
    ((line_continuous.tendsto t).eventually_mem (isOpen_interior.mem_nhds still_inside)).and
      (Iio_mem_nhds before_end)
  obtain ⟨u, later, hu, before_one⟩ := nearby.exists_gt
  have u_in : u ∈ times := ⟨⟨ht.1.1.trans later.le, before_one.le⟩,
    show line u ∈ P.body from interior_subset hu⟩
  exact (not_le_of_gt later) (last u_in)

/-- A nonconstant supporting functional is strictly below its support level in the interior. -/
theorem strict_support_at_interior (P : ConvexPolyhedron) {n : Space} {level : ℝ}
    (nonzero : n ≠ 0) (support : ∀ x ∈ P.body, inner ℝ n x ≤ level)
    {a : Space} (inside : a ∈ interior P.body) : inner ℝ n a < level := by
  have inclusion : P.body ⊆ (innerSL ℝ n) ⁻¹' Set.Iic level := support
  have strict := interior_mono inclusion inside
  rw [(innerSL ℝ n).interior_preimage (inner_height_surjective nonzero), interior_Iic] at strict
  exact strict

/-- Once one supporting inequality has been chosen for each facet, those inequalities define the body. -/
theorem mem_body_iff_facet_inequalities (P : ConvexPolyhedron)
    (normal : P.Face → Space) (level : P.Face → ℝ)
    (nonzero : ∀ F, normal F ≠ 0)
    (support : ∀ F, ∀ x ∈ P.body, inner ℝ (normal F) x ≤ level F)
    (face_eq : ∀ F, F.val = {x ∈ P.body | inner ℝ (normal F) x = level F})
    (z : Space) : z ∈ P.body ↔ ∀ F, inner ℝ (normal F) z ≤ level F := by
  refine ⟨fun member F => support F z member, ?_⟩
  intro inequalities
  by_contra outside
  obtain ⟨a, inside⟩ := P.solid
  obtain ⟨t, t_nonnegative, t_before_one, exit_boundary⟩ := P.segment_exit inside outside
  obtain ⟨F, exit_in_face⟩ := P.boundary_point_in_face exit_boundary
  have exit_height := (face_eq F ▸ exit_in_face).2
  have start_strict := P.strict_support_at_interior (nonzero F) (support F) inside
  have end_bound := inequalities F
  simp only [AffineMap.lineMap_apply_module, inner_add_right, inner_smul_right] at exit_height
  nlinarith

/-- The public convex-hull definition has a finite halfspace representation indexed by its facets. -/
theorem exists_facet_halfspace_representation (P : ConvexPolyhedron) :
    ∃ (normal : P.Face → Space) (level : P.Face → ℝ),
      (∀ F, normal F ≠ 0) ∧
      (∀ F, F.val = {x ∈ P.body | inner ℝ (normal F) x = level F}) ∧
      P.body = {x | ∀ F, inner ℝ (normal F) x ≤ level F} := by
  choose normal level nonzero support face_eq using fun F : P.Face => F.property.2
  exact ⟨normal, level, nonzero, face_eq,
    Set.ext (P.mem_body_iff_facet_inequalities normal level nonzero support face_eq)⟩

end SixVertexUnfolding.ConvexPolyhedron
