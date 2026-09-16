import SixVertexUnfolding.Geometry.PlanarLineParametrization
import SixVertexUnfolding.Geometry.SourceBisectors

/-! Each candidate bisector inside a compact original facet is covered
by a single straight segment whose endpoints remain in that whole facet. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A compact original facet clips a planar bisector to a cofacial segment, possibly empty or a point. -/
theorem face_bisector_segment_cover (P : ConvexPolyhedron) (F : P.Face)
    (p q : Plane) (different : p ≠ q) :
    ∃ u ∈ F.val, ∃ v ∈ F.val, ∀ x ∈ F.val,
      dist p (P.faceCoordinates F x) = dist q (P.faceCoordinates F x) → x ∈ segment ℝ u v := by
  by_cases nonempty : ∃ x ∈ F.val, dist p (P.faceCoordinates F x) = dist q (P.faceCoordinates F x)
  · obtain ⟨x, xF, tie⟩ := nonempty
    obtain ⟨line, isometric, range_eq⟩ := plane_line_parametrization (q - p)
      (sub_ne_zero.mpr different.symm) ((‖q‖ ^ 2 - ‖p‖ ^ 2) / 2) (P.faceCoordinates F x)
      ((equal_site_distances_iff_bisector p q _).mp tie)
    obtain ⟨lift, _, coordinate, inverse, rigid⟩ :=
      F.exists_rigid_plane_inverse (P.faceCoordinates F) (P.faceCoordinates_rigid F)
    let curve := lift.comp line
    have curve_isometric : Isometry curve := (Isometry.of_dist_eq rigid).comp isometric
    have compact : IsCompact (curve ⁻¹' F.val) := curve_isometric.isClosedEmbedding.isCompact_preimage F.isCompact
    have nonempty_parameters : (curve ⁻¹' F.val).Nonempty := by
      have member : P.faceCoordinates F x ∈ range line := by
        rw [range_eq]
        exact (equal_site_distances_iff_bisector p q _).mp tie
      obtain ⟨t, ht⟩ := member
      refine ⟨t, ?_⟩
      change lift (line t) ∈ F.val
      rw [ht, inverse x (subset_affineSpan ℝ _ xF)]
      exact xF
    obtain ⟨l, hl, least⟩ := compact.exists_isMinOn nonempty_parameters continuous_id.continuousOn
    obtain ⟨r, hr, greatest⟩ := compact.exists_isMaxOn nonempty_parameters continuous_id.continuousOn
    have ordered : l ≤ r := least hr
    refine ⟨curve l, hl, curve r, hr, ?_⟩
    intro y yF tied
    have member : P.faceCoordinates F y ∈ range line := by
      rw [range_eq]
      exact (equal_site_distances_iff_bisector p q _).mp tied
    obtain ⟨t, ht⟩ := member
    have curve_t : curve t = y := by
      change lift (line t) = y
      rw [ht, inverse y (subset_affineSpan ℝ _ yF)]
    have parameter : t ∈ curve ⁻¹' F.val := by rw [mem_preimage, curve_t]; exact yF
    rw [← image_segment ℝ curve, segment_eq_Icc ordered]
    exact ⟨t, ⟨least parameter, greatest parameter⟩, curve_t⟩
  · obtain ⟨u, hu⟩ := F.nonempty
    exact ⟨u, hu, u, hu, fun x hx tie => (nonempty ⟨x, hx, tie⟩).elim⟩

end SixVertexUnfolding.ConvexPolyhedron
