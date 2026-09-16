import SixVertexUnfolding.Geometry.NormalizedFacets

/-! The normalized supporting equation describes the entire affine plane of each facet. -/

namespace SixVertexUnfolding.ConvexPolyhedron.NormalizedFacets

variable {P : ConvexPolyhedron} {center : Space} (facets : NormalizedFacets P center)

/-- The normalized support equation holds beyond the polygon, throughout its affine plane. -/
theorem on_plane (F : P.Face) {x : Space} (member : x ∈ affineSpan ℝ F.val) :
    inner ℝ (facets.normal F) (x - center) = 1 := by
  have agree : Set.EqOn (innerSL ℝ (facets.normal F)).toLinearMap.toAffineMap
      (AffineMap.const ℝ Space (1 + inner ℝ (facets.normal F) center)) F.val := by
    intro y hy
    have value := facets.on_face F hy
    change inner ℝ (facets.normal F) y = 1 + inner ℝ (facets.normal F) center
    rw [inner_sub_right] at value
    linarith
  have value := AffineMap.eqOn_affineSpan agree member
  change inner ℝ (facets.normal F) x = 1 + inner ℝ (facets.normal F) center at value
  rw [inner_sub_right]
  linarith

/-- A normalized facet normal cannot vanish. -/
theorem normal_ne_zero (F : P.Face) : facets.normal F ≠ 0 := by
  obtain ⟨x, hx⟩ := F.nonempty
  have value := facets.on_face F hx
  intro zero
  simp [zero] at value

/-- The facet direction consists exactly of the vectors perpendicular to its supporting normal. -/
theorem direction_eq_orthogonal (F : P.Face) :
    (affineSpan ℝ F.val).direction = (Submodule.span ℝ {facets.normal F})ᗮ := by
  obtain ⟨a, ha⟩ := F.nonempty
  have a_plane := subset_affineSpan ℝ _ ha
  have inclusion : (affineSpan ℝ F.val).direction ≤ (Submodule.span ℝ {facets.normal F})ᗮ := by
    intro v hv
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    have shifted := facets.on_plane F (AffineSubspace.vadd_mem_of_mem_direction hv a_plane)
    have original := facets.on_face F ha
    change inner ℝ (facets.normal F) ((v + a) - center) = 1 at shifted
    rw [inner_sub_right, inner_add_right] at shifted
    rw [inner_sub_right] at original
    linarith
  have sum := (Submodule.span ℝ {facets.normal F}).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton (facets.normal_ne_zero F)] at sum
  have ambient : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [ambient] at sum
  apply Submodule.eq_of_le_of_finrank_eq inclusion
  have dimension : Module.finrank ℝ (affineSpan ℝ F.val).direction = 2 := F.property.1
  omega

/-- The supporting equation also suffices for membership in the extended facet plane. -/
theorem mem_plane_iff (F : P.Face) (x : Space) :
    x ∈ affineSpan ℝ F.val ↔ inner ℝ (facets.normal F) (x - center) = 1 := by
  refine ⟨facets.on_plane F, ?_⟩
  intro value
  obtain ⟨a, ha⟩ := F.nonempty
  have original := facets.on_face F ha
  have tangent : x - a ∈ (affineSpan ℝ F.val).direction := by
    rw [facets.direction_eq_orthogonal F]
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [inner_sub_right] at value original ⊢
    linarith
  simpa only [vadd_eq_add, sub_add_cancel] using
    AffineSubspace.vadd_mem_of_mem_direction tangent (subset_affineSpan ℝ _ ha)

/-- Measured from any point of a supporting plane, every point of the solid has nonpositive height. -/
theorem difference_nonpositive (F : P.Face) {o x : Space}
    (ho : o ∈ affineSpan ℝ F.val) (hx : x ∈ P.body) :
    inner ℝ (facets.normal F) (x - o) ≤ 0 := by
  have origin := facets.on_plane F ho
  have bound := facets.support F x hx
  rw [inner_sub_right] at origin bound ⊢
  linarith

/-- A solid point outside the facet has strictly negative height from its supporting plane. -/
theorem difference_negative (F : P.Face) {o x : Space}
    (ho : o ∈ affineSpan ℝ F.val) (hx : x ∈ P.body) (outside : x ∉ F.val) :
    inner ℝ (facets.normal F) (x - o) < 0 := by
  apply lt_of_le_of_ne (facets.difference_nonpositive F ho hx)
  intro equal
  apply outside
  rw [facets.face_eq F]
  refine ⟨hx, ?_⟩
  have origin := facets.on_plane F ho
  rw [inner_sub_right] at origin equal ⊢
  linarith

/-- Differences within a facet plane have zero supporting height. -/
theorem difference_zero (F : P.Face) {o x : Space}
    (ho : o ∈ affineSpan ℝ F.val) (hx : x ∈ affineSpan ℝ F.val) :
    inner ℝ (facets.normal F) (x - o) = 0 := by
  have origin := facets.on_plane F ho
  have point := facets.on_plane F hx
  rw [inner_sub_right] at origin point ⊢
  linarith

end SixVertexUnfolding.ConvexPolyhedron.NormalizedFacets
