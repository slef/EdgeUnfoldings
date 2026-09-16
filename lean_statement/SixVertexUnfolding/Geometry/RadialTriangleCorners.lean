import SixVertexUnfolding.Geometry.RadialSectorMembership
import SixVertexUnfolding.Geometry.CounterclockwiseAngle
import SixVertexUnfolding.Geometry.TriangleHalfplanes

/-! Directions of points in a triangle give explicit lower bounds for exterior corners. -/

namespace SixVertexUnfolding

open Real

/-- Choosing a half-open turn removes the duplicate endpoint direction. -/
theorem polar_representation_in_half_open_turn (α : ℝ) (x : Plane) (nonzero : x ≠ 0) :
    ∃ θ, α ≤ θ ∧ θ < α + 2 * π ∧ x = dist 0 x • direction θ := by
  obtain ⟨θ, lower, upper, representation⟩ := polar_representation_in_turn α x nonzero
  rcases upper.eq_or_lt with equal | strict
  · refine ⟨α, le_rfl, by linarith [pi_pos], ?_⟩
    simpa only [equal, direction_add_two_pi] using representation
  · exact ⟨θ, lower, strict, representation⟩

/-- The polar representative of a nonzero point lies in the triangle's actual sector. -/
theorem radial_triangle_polar_representation (r s α β : ℝ) (r_pos : 0 < r) (s_pos : 0 < s)
    (ordered : α < β) (width : β - α < π) (x : Plane) (nonzero : x ≠ 0)
    (member : x ∈ convexHull ℝ ({0, r • direction α, s • direction β} : Set Plane)) :
    ∃ θ, α ≤ θ ∧ θ ≤ β ∧ x = dist 0 x • direction θ := by
  obtain ⟨θ, lower, upper, representation⟩ := polar_representation_in_half_open_turn α x nonzero
  refine ⟨θ, lower, ?_, representation⟩
  apply radial_triangle_polar_sector r s (dist 0 x) α β θ r_pos s_pos
    (dist_pos.mpr nonzero.symm) ordered width upper
  rwa [← representation]

/-- Translate a triangle to one of its vertices using its barycentric weights. -/
theorem triangle_sub_vertex (a b c x : Plane)
    (member : x ∈ convexHull ℝ ({a, b, c} : Set Plane)) :
    x - a ∈ convexHull ℝ ({0, b - a, c - a} : Set Plane) := by
  obtain ⟨u, v, z, hu, hv, hz, total, expression⟩ := triangle_weights a b c x member
  apply triangle_mem_of_weights 0 (b - a) (c - a) (x - a) u v z hu hv hz total
  rw [← expression]
  have scaled := congrArg (fun t : ℝ => t • a) total
  simp only [add_smul, one_smul] at scaled
  simp only [smul_zero, smul_sub, zero_add]
  ext i
  have coordinate := congrArg (fun v : Plane => v i) scaled
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at coordinate ⊢
  linarith

/-- The exterior angle from the later pole ray contains the whole complementary sector. -/
theorem counterclockwiseAngle_from_later_ray (r s t α β γ : ℝ)
    (r_pos : 0 < r) (s_pos : 0 < s) (t_pos : 0 < t)
    (ordered : α < β) (width : β - α < π) (later : β < γ) (one_turn : γ < α + 2 * π)
    (x : Plane) (nonzero : x ≠ 0)
    (member : x ∈ convexHull ℝ ({0, r • direction α, s • direction β} : Set Plane)) :
    2 * π + α - γ ≤ counterclockwiseAngle (t • direction γ) x := by
  obtain ⟨θ, lower, upper, representation⟩ :=
    radial_triangle_polar_representation r s α β r_pos s_pos ordered width x nonzero member
  have periodic : direction (γ - 2 * π) = direction γ := by
    have identity := direction_add_two_pi (γ - 2 * π)
    simpa only [sub_add_cancel] using identity.symm
  have measured := counterclockwiseAngle_polar t (dist 0 x) (γ - 2 * π) θ t_pos
    (dist_pos.mpr nonzero.symm) (by linarith) (by linarith)
  rw [periodic, ← representation] at measured
  linarith

/-- The exterior angle to the earlier pole ray contains the whole complementary sector. -/
theorem counterclockwiseAngle_to_earlier_ray (r s t α β γ : ℝ)
    (r_pos : 0 < r) (s_pos : 0 < s) (t_pos : 0 < t)
    (ordered : α < β) (width : β - α < π) (earlier : γ < α) (one_turn : β < γ + 2 * π)
    (x : Plane) (nonzero : x ≠ 0)
    (member : x ∈ convexHull ℝ ({0, r • direction α, s • direction β} : Set Plane)) :
    2 * π + γ - β ≤ counterclockwiseAngle x (t • direction γ) := by
  obtain ⟨θ, lower, upper, representation⟩ :=
    radial_triangle_polar_representation r s α β r_pos s_pos ordered width x nonzero member
  have measured := counterclockwiseAngle_polar (dist 0 x) t θ (γ + 2 * π)
    (dist_pos.mpr nonzero.symm) t_pos (by linarith) (by linarith)
  rw [direction_add_two_pi, ← representation] at measured
  linarith

end SixVertexUnfolding
