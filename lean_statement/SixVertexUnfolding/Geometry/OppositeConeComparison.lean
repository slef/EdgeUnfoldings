import SixVertexUnfolding.Geometry.TwoRayCones
import SixVertexUnfolding.Geometry.TriangleDistanceSum

/-! The distance-sum proof that two short copied cut edges cannot make their opposite apex cones overlap. -/

namespace SixVertexUnfolding

theorem triangle_distance_sum_lt_of_noncollinear (a b c m : Plane)
    (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Plane))
    (contained : m ∈ convexHull ℝ ({a, b, c} : Set Plane)) (not_apex : m ≠ c) :
    dist m a + dist m b < dist c a + dist c b := by
  apply triangle_distance_sum_lt a b c m _ contained not_apex
  have strict : dist a b < dist a c + dist c b := by
    apply dist_lt_dist_add_dist_iff.mpr
    intro between
    apply noncollinear
    have reorder : ({a, c, b} : Set Plane) = {a, b, c} := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [← reorder]
    exact between.collinear
  simpa only [dist_comm a c] using strict

/-- The middle apex lies strictly below the virtual cut-ray intersection in distance sum.
This separates the two entire translated cones, not just the copied cut segments. -/
theorem opposite_cones_disjoint_from_virtual_triangle (a b c m p q e f : Plane)
    (independent : det e f ≠ 0) (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Plane))
    (contained : m ∈ convexHull ℝ ({a, b, c} : Set Plane)) (not_apex : m ≠ c)
    (left_copy : p = a - dist m a • e) (right_copy : q = b + dist m b • f)
    (virtual_left : c = a - dist c a • e) (virtual_right : c = b + dist c b • f) :
    Disjoint (translatedCone p e f) (translatedCone q (-e) (-f)) := by
  apply opposed_cones_disjoint_of_lengths p q e f independent (dist m a) (dist m b) (dist c a) (dist c b)
  · have left_arm : a - p = dist m a • e := by rw [left_copy]; module
    have right_arm : q - b = dist m b • f := by rw [right_copy]; module
    have first : c - a = -(dist c a • e) := by nth_rw 1 [virtual_left]; module
    have second : b - c = -(dist c b • f) := by nth_rw 1 [virtual_right]; module
    calc
      q - p = (q - b) + (b - c) + (c - a) + (a - p) := by module
      _ = (dist m a - dist c a) • e + (dist m b - dist c b) • f := by
        rw [right_arm, second, first, left_arm]
        module
  · exact triangle_distance_sum_lt_of_noncollinear a b c m noncollinear contained not_apex

end SixVertexUnfolding
