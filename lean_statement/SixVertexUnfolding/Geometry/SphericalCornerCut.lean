import SixVertexUnfolding.Geometry.SphericalSpan

/-! Angular perimeter estimates for the remaining five-ray argument:
a triangle in an open hemisphere has perimeter below a full turn, and
cutting off a convex corner cannot increase angular perimeter. -/

namespace SixVertexUnfolding

open InnerProductGeometry

/-- Three positive-height directions have angular perimeter strictly below two pi. -/
theorem spherical_triangle_perimeter_lt (height : Space →ₗ[ℝ] ℝ) (a b c : Space)
    (ha : 0 < height a) (hb : 0 < height b) (hc : 0 < height c) :
    angle a b + angle b c + angle c a < 2 * Real.pi := by
  have nonzero : a ≠ 0 := by intro zero; simp only [zero, map_zero, lt_self_iff_false] at ha
  have strict := angle_triangle_strict_of_height height b (-a) c hb hc
    (by rw [map_neg]; linarith) (neg_ne_zero.mpr nonzero)
  rw [angle_neg_right, angle_neg_left, angle_comm b a] at strict
  rw [angle_comm c a]
  linarith

/-- Replacing a corner by a chord between its two incident sides shortens angular perimeter. -/
theorem spherical_corner_cut_le (a b c x y : Space) (x_ne : x ≠ 0) (y_ne : y ≠ 0)
    (left : x ∈ segment ℝ a b) (right : y ∈ segment ℝ b c) :
    angle a x + angle x y + angle y c ≤ angle a b + angle b c := by
  have first := angle_add_of_segment a b x x_ne left
  have second := angle_add_of_segment b c y y_ne right
  have chord := angle_le_angle_add_angle x b y
  linarith

/-- The polygon retained after cutting a triangle corner has no larger angular perimeter. -/
theorem spherical_triangle_corner_cut_le (a b c x y : Space) (x_ne : x ≠ 0) (y_ne : y ≠ 0)
    (left : x ∈ segment ℝ a b) (right : y ∈ segment ℝ b c) :
    angle a x + angle x y + angle y c + angle c a ≤
      angle a b + angle b c + angle c a := by
  linarith [spherical_corner_cut_le a b c x y x_ne y_ne left right]

/-- A pentagon obtained by two corner cuts inherits the strict hemisphere perimeter bound.
The enclosing triangle and cut incidences are explicit hypotheses here. -/
theorem spherical_pentagon_two_cuts_lt (height : Space →ₗ[ℝ] ℝ)
    (a b c x y z w : Space) (ha : 0 < height a) (hb : 0 < height b) (hc : 0 < height c)
    (x_ne : x ≠ 0) (y_ne : y ≠ 0) (z_ne : z ≠ 0) (w_ne : w ≠ 0)
    (x_side : x ∈ segment ℝ a b) (y_side : y ∈ segment ℝ b c)
    (z_side : z ∈ segment ℝ y c) (w_side : w ∈ segment ℝ c a) :
    angle a x + angle x y + angle y z + angle z w + angle w a < 2 * Real.pi := by
  have first := spherical_corner_cut_le a b c x y x_ne y_ne x_side y_side
  have second := spherical_corner_cut_le y c a z w z_ne w_ne z_side w_side
  have triangle := spherical_triangle_perimeter_lt height a b c ha hb hc
  linarith

end SixVertexUnfolding
