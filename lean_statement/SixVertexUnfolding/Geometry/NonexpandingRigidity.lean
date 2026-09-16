import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.Convex.Hull
import SixVertexUnfolding.Geometry.Polyhedron

/-! A nonexpanding map fixing the corners fixes their convex hull.
This lets local triangle foldings inherit their common flat coordinates. -/

namespace SixVertexUnfolding

open Set

/-- The fixed points of a nonexpanding map on a convex Euclidean region are convex. -/
theorem nonexpanding_fixed_points_convex (region : Set Plane) (convex_region : Convex ℝ region)
    (f : region → Plane) (bound : LipschitzWith 1 f) :
    Convex ℝ {x | ∃ inside : x ∈ region, f ⟨x, inside⟩ = x} := by
  apply convex_iff_segment_subset.mpr
  rintro x ⟨hx, fixed_x⟩ y ⟨hy, fixed_y⟩ z hz
  have inside := convex_region.segment_subset hx hy hz
  refine ⟨inside, ?_⟩
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have left_bound := bound.dist_le_mul (⟨x, hx⟩ : region) ⟨_, inside⟩
  have right_bound := bound.dist_le_mul (⟨_, inside⟩ : region) ⟨y, hy⟩
  simp only [fixed_x, fixed_y, NNReal.coe_one, one_mul, Subtype.dist_eq] at left_bound right_bound
  rw [dist_left_lineMap, Real.norm_of_nonneg ht.1] at left_bound
  rw [dist_lineMap_right, Real.norm_of_nonneg (sub_nonneg.mpr ht.2)] at right_bound
  have triangle := dist_triangle x (f ⟨_, inside⟩) y
  apply eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
  · linarith
  · linarith

/-- Fixing a generating set is enough; no injectivity or affine hypothesis is assumed. -/
theorem nonexpanding_eq_on_convexHull (corners region : Set Plane)
    (convex_region : Convex ℝ region) (contained : corners ⊆ region)
    (f : region → Plane) (bound : LipschitzWith 1 f)
    (fixed : ∀ x (member : x ∈ corners), f ⟨x, contained member⟩ = x) :
    ∀ x (inside : x ∈ convexHull ℝ corners),
      f ⟨x, convexHull_min contained convex_region inside⟩ = x := by
  have hull := convexHull_min
    (show corners ⊆ {x | ∃ inside : x ∈ region, f ⟨x, inside⟩ = x} from
      fun x hx => ⟨contained hx, fixed x hx⟩)
    (nonexpanding_fixed_points_convex region convex_region f bound)
  intro x inside
  exact (hull inside).choose_spec

end SixVertexUnfolding
