import SixVertexUnfolding.Geometry.FiveRayEnclosure
import SixVertexUnfolding.Geometry.SphericalCornerCut

/-! Strict angular deficit for every supported five-ray figure.
Construct an enclosing triangle, then shorten its perimeter by two cuts. -/

namespace SixVertexUnfolding.FiveRayFan

open InnerProductGeometry

/-- Cyclic relabelling preserves the total sector angle. -/
theorem sum_angles_rotate (fan : FiveRayFan) (i : Fin 5) :
    (∑ j : Fin 5, angle ((fan.rotate i).ray j) ((fan.rotate i).ray (j + 1))) =
      ∑ j : Fin 5, angle (fan.ray j) (fan.ray (j + 1)) := by
  simpa only [rotate, Equiv.coe_addLeft, add_assoc] using
    Equiv.sum_comp (Equiv.addLeft i) (fun j => angle (fan.ray j) (fan.ray (j + 1)))

/-- The five surface sectors sum to strictly less than a full turn. -/
theorem sum_angles_lt_two_pi (fan : FiveRayFan) :
    ∑ i : Fin 5, angle (fan.ray i) (fan.ray (i + 1)) < 2 * Real.pi := by
  obtain ⟨i, b, c, bh, ch, x_side, y_side, z_side, w_side⟩ := fan.exists_enclosing_triangle
  let g := fan.rotate i
  have nonzero (j : Fin 5) : g.ray j ≠ 0 := by
    intro zero
    have level := g.level j
    rw [zero, map_zero] at level
    norm_num at level
  have bound := spherical_pentagon_two_cuts_lt g.height (g.ray 0) b c
    (g.ray 1) (g.ray 2) (g.ray 3) (g.ray 4)
    (by rw [g.level]; norm_num) (by rw [bh]; norm_num) (by rw [ch]; norm_num)
    (nonzero 1) (nonzero 2) (nonzero 3) (nonzero 4) x_side y_side z_side w_side
  have sum_bound : (∑ j : Fin 5, angle (g.ray j) (g.ray (j + 1))) < 2 * Real.pi := by
    simpa [Fin.sum_univ_succ, add_assoc] using bound
  rwa [sum_angles_rotate] at sum_bound

/-- The same strict bound with all five sectors written out. -/
theorem perimeter_lt_two_pi (fan : FiveRayFan) :
    angle (fan.ray 0) (fan.ray 1) + angle (fan.ray 1) (fan.ray 2) +
      angle (fan.ray 2) (fan.ray 3) + angle (fan.ray 3) (fan.ray 4) +
      angle (fan.ray 4) (fan.ray 0) < 2 * Real.pi := by
  simpa [Fin.sum_univ_succ, add_assoc] using fan.sum_angles_lt_two_pi

end SixVertexUnfolding.FiveRayFan
