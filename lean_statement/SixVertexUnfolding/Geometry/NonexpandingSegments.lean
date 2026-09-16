import SixVertexUnfolding.Definitions
import Mathlib.Analysis.Convex.StrictConvexBetween

/-! A nonexpanding map that preserves a segment's endpoint distance
must map that whole segment affinely. This gives actual straight radial
segments when a triangle folds near a surface vertex. -/

namespace SixVertexUnfolding

open Set

/-- Equality at the endpoints forces equality throughout the segment. -/
theorem nonexpanding_lineMap {region : Set Plane} (convex_region : Convex ℝ region)
    (fold : region → Space) (nonexpanding : LipschitzWith 1 fold)
    (x y : region) (distance : dist (fold x) (fold y) = dist (x : Plane) y)
    (t : ℝ) (between : t ∈ Icc (0 : ℝ) 1) :
    fold ⟨AffineMap.lineMap (x : Plane) y t, convex_region.mapsTo_lineMap x.property y.property between⟩ =
      AffineMap.lineMap (fold x) (fold y) t := by
  let z : region := ⟨AffineMap.lineMap (x : Plane) y t,
    convex_region.mapsTo_lineMap x.property y.property between⟩
  have first : dist (fold x) (fold z) ≤ t * dist (x : Plane) y := by
    have bound := nonexpanding.dist_le_mul x z
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, z,
      dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg between.1] using bound
  have second : dist (fold z) (fold y) ≤ (1 - t) * dist (x : Plane) y := by
    have bound := nonexpanding.dist_le_mul z y
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, z,
      dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr between.2)] using bound
  have total := dist_triangle (fold x) (fold z) (fold y)
  rw [distance] at total
  apply eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
  · rw [distance]
    linarith
  · rw [distance]
    linarith

end SixVertexUnfolding
