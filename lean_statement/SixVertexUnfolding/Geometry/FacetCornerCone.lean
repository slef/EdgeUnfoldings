import SixVertexUnfolding.Geometry.FacetCoordinates
import SixVertexUnfolding.Geometry.TriangleCones

/-! Supporting planes contain each polygon in its actual or extended corner cone. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- Three noncollinear points in the facet plane span it, even if the points lie outside the polygon. -/
theorem plane_triangle_spans (o a b : Space)
    (ho : o ∈ affineSpan ℝ F.val) (ha : a ∈ affineSpan ℝ F.val) (hb : b ∈ affineSpan ℝ F.val)
    (noncollinear : ¬ Collinear ℝ ({o, a, b} : Set Space)) :
    affineSpan ℝ ({o, a, b} : Set Space) = affineSpan ℝ F.val := by
  have inclusion : affineSpan ℝ ({o, a, b} : Set Space) ≤ affineSpan ℝ F.val := by
    apply affineSpan_le_of_subset_coe
    rintro x (rfl | rfl | rfl)
    exacts [ho, ha, hb]
  have upper := Submodule.finrank_mono (AffineSubspace.direction_le inclusion)
  have lower : ¬ Module.finrank ℝ (affineSpan ℝ ({o, a, b} : Set Space)).direction ≤ 1 := by
    intro small
    apply noncollinear
    apply collinear_iff_finrank_le_one.mpr
    rwa [direction_affineSpan] at small
  have dimension : Module.finrank ℝ (affineSpan ℝ F.val).direction = 2 := F.property.1
  have equal_dimension : Module.finrank ℝ (affineSpan ℝ ({o, a, b} : Set Space)).direction =
      Module.finrank ℝ (affineSpan ℝ F.val).direction := by omega
  exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le inclusion) equal_dimension)
    ((show ({o, a, b} : Set Space).Nonempty from ⟨o, by simp⟩).affineSpan ℝ) inclusion

/-- Coordinates based at a virtual corner are valid throughout the facet plane. -/
theorem plane_triangle_coordinates_of_mem_plane (o a b x : Space)
    (ho : o ∈ affineSpan ℝ F.val) (ha : a ∈ affineSpan ℝ F.val) (hb : b ∈ affineSpan ℝ F.val)
    (noncollinear : ¬ Collinear ℝ ({o, a, b} : Set Space)) (hx : x ∈ affineSpan ℝ F.val) :
    ∃ t u : ℝ, x - o = t • (a - o) + u • (b - o) := by
  have member : x ∈ affineSpan ℝ ({o, a, b} : Set Space) := by
    rw [F.plane_triangle_spans o a b ho ha hb noncollinear]
    exact hx
  have origin := subset_affineSpan ℝ ({o, a, b} : Set Space) (by simp : o ∈ ({o, a, b} : Set Space))
  have difference := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan member origin
  rw [vectorSpan_eq_span_vsub_set_right ℝ (by simp : o ∈ ({o, a, b} : Set Space))] at difference
  simp only [Set.image_insert_eq, Set.image_singleton, vsub_eq_sub, sub_self,
    Submodule.span_insert_zero] at difference
  obtain ⟨t, u, equal⟩ := Submodule.mem_span_pair.mp difference
  exact ⟨t, u, equal.symm⟩

/-- In particular, these coordinates apply to every point of the polygon. -/
theorem plane_triangle_coordinates (o a b x : Space)
    (ho : o ∈ affineSpan ℝ F.val) (ha : a ∈ affineSpan ℝ F.val) (hb : b ∈ affineSpan ℝ F.val)
    (noncollinear : ¬ Collinear ℝ ({o, a, b} : Set Space)) (hx : x ∈ F.val) :
    ∃ t u : ℝ, x - o = t • (a - o) + u • (b - o) :=
  F.plane_triangle_coordinates_of_mem_plane o a b x ho ha hb noncollinear (subset_affineSpan ℝ _ hx)

/-- Two supporting inequalities force both coordinates in the corner cone to be nonnegative. -/
theorem nonnegative_corner_coordinates (o a b x : Space)
    (ho : o ∈ affineSpan ℝ F.val) (ha : a ∈ affineSpan ℝ F.val) (hb : b ∈ affineSpan ℝ F.val)
    (noncollinear : ¬ Collinear ℝ ({o, a, b} : Set Space))
    (first second : Space →ₗ[ℝ] ℝ)
    (first_axis : first (a - o) = 0) (first_inside : first (b - o) < 0)
    (second_axis : second (b - o) = 0) (second_inside : second (a - o) < 0)
    (hx : x ∈ F.val) (first_bound : first (x - o) ≤ 0) (second_bound : second (x - o) ≤ 0) :
    ∃ t u : ℝ, 0 ≤ t ∧ 0 ≤ u ∧ x - o = t • (a - o) + u • (b - o) := by
  obtain ⟨t, u, coordinates⟩ := F.plane_triangle_coordinates o a b x ho ha hb noncollinear hx
  rw [coordinates, map_add, map_smul, map_smul, first_axis, smul_eq_mul, smul_eq_mul, mul_zero, zero_add] at first_bound
  rw [coordinates, map_add, map_smul, map_smul, second_axis, smul_eq_mul, smul_eq_mul, mul_zero, add_zero] at second_bound
  exact ⟨t, u, by nlinarith, by nlinarith, coordinates⟩

/-- After any affine placement, the whole polygon remains inside the cone bounded by its supporting lines. -/
theorem placed_in_corner_cone (place : Space →ᵃ[ℝ] Plane) (o a b : Space)
    (ho : o ∈ affineSpan ℝ F.val) (ha : a ∈ affineSpan ℝ F.val) (hb : b ∈ affineSpan ℝ F.val)
    (noncollinear : ¬ Collinear ℝ ({o, a, b} : Set Space))
    (first second : Space →ₗ[ℝ] ℝ)
    (first_axis : first (a - o) = 0) (first_inside : first (b - o) < 0)
    (second_axis : second (b - o) = 0) (second_inside : second (a - o) < 0)
    (first_support : ∀ x ∈ F.val, first (x - o) ≤ 0)
    (second_support : ∀ x ∈ F.val, second (x - o) ≤ 0) :
    place '' F.val ⊆ translatedCone (place o) (place a - place o) (place b - place o) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨t, u, ht, hu, coordinates⟩ := F.nonnegative_corner_coordinates o a b x
    ho ha hb noncollinear first second first_axis first_inside second_axis second_inside
    hx (first_support x hx) (second_support x hx)
  refine ⟨t, u, ht, hu, ?_⟩
  have mapped := congrArg place.linear coordinates
  have map_difference (v w : Space) : place.linear (v - w) = place v - place w :=
    place.linearMap_vsub v w
  simpa only [map_add, map_smul, map_difference] using mapped

end SixVertexUnfolding.ConvexPolyhedron.Face
