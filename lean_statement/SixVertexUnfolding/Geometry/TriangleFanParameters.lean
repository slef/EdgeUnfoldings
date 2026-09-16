import SixVertexUnfolding.Geometry.JoinedTriangles
import SixVertexUnfolding.Geometry.PlaneOrientation
import Mathlib.Topology.UnitInterval

/-! A triangle is parametrized by a point of its base and a fraction
of the straight ray from its apex. Only the zero-time base is collapsed. -/

namespace SixVertexUnfolding

open Set

/-- The usual radial parametrization of a closed planar triangle. -/
noncomputable def triangleFanMap (p u v : Plane) : C(unitInterval × unitInterval, Plane) :=
  ⟨fun z => AffineMap.lineMap p (AffineMap.lineMap u v (z.1 : ℝ)) (z.2 : ℝ), by
    simp only [AffineMap.lineMap_apply_module]
    fun_prop⟩

theorem triangleFan_height (p u v : Plane) (z : unitInterval × unitInterval) :
    det (v - u) (triangleFanMap p u v z - u) = (1 - (z.2 : ℝ)) * det (v - u) (p - u) := by
  apply triangle_weighted_area u v p _ ((z.2 : ℝ) * (1 - (z.1 : ℝ)))
    ((z.2 : ℝ) * (z.1 : ℝ)) (1 - (z.2 : ℝ)) (by ring)
  change _ = AffineMap.lineMap p (AffineMap.lineMap u v (z.1 : ℝ)) (z.2 : ℝ)
  simp only [AffineMap.lineMap_apply_module, smul_add, smul_smul]
  module

/-- The radial square covers exactly the closed triangle. -/
theorem triangleFan_range (p u v : Plane) :
    range (triangleFanMap p u v) = convexHull ℝ ({p, u, v} : Set Plane) := by
  ext x
  constructor
  · rintro ⟨⟨b, t⟩, rfl⟩
    have base : AffineMap.lineMap u v (b : ℝ) ∈ segment ℝ u v := by
      rw [segment_eq_image_lineMap]
      exact ⟨b, b.property, rfl⟩
    have base_in : AffineMap.lineMap u v (b : ℝ) ∈ convexHull ℝ ({p, u, v} : Set Plane) :=
      (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ (by simp))
        (subset_convexHull ℝ _ (by simp)) base
    apply (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (by simp : p ∈ ({p, u, v} : Set Plane))) base_in
    rw [segment_eq_image_lineMap]
    exact ⟨t, t.property, rfl⟩
  · intro inside
    rw [convexHull_insert (insert_nonempty u {v}), convexHull_pair] at inside
    obtain ⟨a, ha, y, hy, on_segment⟩ := mem_convexJoin.mp inside
    have ap : a = p := ha
    rw [ap, segment_eq_image_lineMap] at on_segment
    rw [segment_eq_image_lineMap] at hy
    obtain ⟨b, hb, at_b⟩ := hy
    obtain ⟨t, ht, at_t⟩ := on_segment
    exact ⟨(⟨b, hb⟩, ⟨t, ht⟩), by change AffineMap.lineMap p (AffineMap.lineMap u v b) t = x; rwa [at_b]⟩

/-- Nondegeneracy makes the radial coordinates unique except at the common apex. -/
theorem triangleFan_fibers (p u v : Plane) (noncollinear : ¬ Collinear ℝ ({u, v, p} : Set Plane))
    (x y : unitInterval × unitInterval) :
    triangleFanMap p u v x = triangleFanMap p u v y ↔ (x.2 = 0 ∧ y.2 = 0) ∨ x = y := by
  have area_ne := det_ne_zero_of_noncollinear u v p noncollinear
  have base : u ≠ v := ne₁₂_of_not_collinear noncollinear
  constructor
  · intro same
    have heights := congrArg (fun w => det (v - u) (w - u)) same
    change det (v - u) (triangleFanMap p u v x - u) = det (v - u) (triangleFanMap p u v y - u) at heights
    rw [triangleFan_height, triangleFan_height] at heights
    have times : x.2 = y.2 := Subtype.ext (by
      have equal := mul_right_cancel₀ area_ne heights
      linarith)
    by_cases zero : x.2 = 0
    · exact Or.inl ⟨zero, times ▸ zero⟩
    · right
      have scalar_ne : (x.2 : ℝ) ≠ 0 := fun h => zero (Subtype.ext h)
      change AffineMap.lineMap p (AffineMap.lineMap u v (x.1 : ℝ)) (x.2 : ℝ) =
        AffineMap.lineMap p (AffineMap.lineMap u v (y.1 : ℝ)) (y.2 : ℝ) at same
      rw [← times] at same
      simp only [AffineMap.lineMap_apply_module] at same
      have positions := smul_right_injective (M := Plane) scalar_ne (add_left_cancel same)
      apply Prod.ext ?_ times
      apply Subtype.ext
      exact AffineMap.lineMap_injective ℝ base (by simpa only [AffineMap.lineMap_apply_module] using positions)
  · rintro (⟨hx, hy⟩ | rfl)
    · change AffineMap.lineMap p _ (x.2 : ℝ) = AffineMap.lineMap p _ (y.2 : ℝ)
      rw [hx, hy]
      simp
    · rfl

end SixVertexUnfolding
