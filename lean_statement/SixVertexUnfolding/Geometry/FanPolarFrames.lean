import SixVertexUnfolding.Geometry.ThreeTriangleChain
import SixVertexUnfolding.Geometry.FourTriangleChain
import SixVertexUnfolding.Geometry.PolarPointUniqueness

/-! Propagate polar coordinates along an outward fan in a prescribed rigid frame.
The frame may put the fan's center anywhere in the plane. -/

namespace SixVertexUnfolding

open Real EuclideanGeometry

/-- An outward corner increases the direction in any rigid frame. -/
theorem outward_motion_point (motion : Plane ≃ᵃⁱ[ℝ] Plane) (a b c d : Plane)
    (α β φ : ℝ) (ab : 0 < dist a b) (ac : 0 < dist a c) (ad : 0 < dist a d)
    (first_pos : 0 < β - α) (first_small : β - α < π)
    (corner_pos : 0 < φ) (corner_small : φ < π)
    (previous : motion b - motion a = dist a b • direction α)
    (shared : motion c - motion a = dist a c • direction β)
    (corner : angle c a d = φ) (outward : OppositeHingeSides a c b d) :
    motion d - motion a = dist a d • direction (β + φ) := by
  let frame := motion.trans (AffineIsometryEquiv.vaddConst ℝ (-motion a))
  have shifted (x : Plane) : frame x = motion x - motion a := by simp [frame, sub_eq_add_neg]
  have center : frame a = 0 := by rw [shifted, sub_self]
  have at_b : frame b = dist a b • direction α := (shifted b).trans previous
  have at_c : frame c = dist a c • direction β := (shifted c).trans shared
  rw [← shifted d]
  apply outward_radial_point _ _ _ α β φ ab ac ad first_pos first_small corner_pos corner_small
  · rw [← center, frame.dist_map]
  · have mapped := frame.toAffineIsometry.angle_map c a d
    change angle (frame c) (frame a) (frame d) = angle c a d at mapped
    simpa only [at_c, center, corner] using mapped
  · simpa only [center, at_b, at_c] using
      (oppositeHingeSides_motion frame a c b d).mpr outward

/-- The reflected orientation decreases the direction. -/
theorem outward_motion_point_down (motion : Plane ≃ᵃⁱ[ℝ] Plane) (a b c d : Plane)
    (α β φ : ℝ) (ab : 0 < dist a b) (ac : 0 < dist a c) (ad : 0 < dist a d)
    (first_pos : 0 < α - β) (first_small : α - β < π)
    (corner_pos : 0 < φ) (corner_small : φ < π)
    (previous : motion b - motion a = dist a b • direction α)
    (shared : motion c - motion a = dist a c • direction β)
    (corner : angle c a d = φ) (outward : OppositeHingeSides a c b d) :
    motion d - motion a = dist a d • direction (β - φ) := by
  let frame := motion.trans (AffineIsometryEquiv.vaddConst ℝ (-motion a))
  have shifted (x : Plane) : frame x = motion x - motion a := by simp [frame, sub_eq_add_neg]
  have center : frame a = 0 := by rw [shifted, sub_self]
  have at_b : frame b = dist a b • direction α := (shifted b).trans previous
  have at_c : frame c = dist a c • direction β := (shifted c).trans shared
  rw [← shifted d]
  apply outward_radial_point_down _ _ _ α β φ ab ac ad first_pos first_small corner_pos corner_small
  · rw [← center, frame.dist_map]
  · have mapped := frame.toAffineIsometry.angle_map c a d
    change angle (frame c) (frame a) (frame d) = angle c a d at mapped
    simpa only [at_c, center, corner] using mapped
  · simpa only [center, at_b, at_c] using
      (oppositeHingeSides_motion frame a c b d).mpr outward

namespace ThreeTriangleChain

/-- Two aligned rays determine every ray in the prescribed counterclockwise frame. -/
theorem polar_motion_up (chain : ThreeTriangleChain) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (θ : Fin 4 → ℝ) (steps : ∀ i : Fin 3, θ i.succ - θ i.castSucc = chain.corner i)
    (first : motion (chain.ray 0) - motion chain.center = chain.radius 0 • direction (θ 0))
    (second : motion (chain.ray 1) - motion chain.center = chain.radius 1 • direction (θ 1)) :
    ∀ i, motion (chain.ray i) - motion chain.center = chain.radius i • direction (θ i) := by
  have next (i : Fin 2)
      (previous : motion (chain.ray i.castSucc.castSucc) - motion chain.center =
        chain.radius i.castSucc.castSucc • direction (θ i.castSucc.castSucc))
      (shared : motion (chain.ray i.succ.castSucc) - motion chain.center =
        chain.radius i.succ.castSucc • direction (θ i.succ.castSucc)) :
      motion (chain.ray i.succ.succ) - motion chain.center =
        chain.radius i.succ.succ • direction (θ i.succ.succ) := by
    have delta : θ i.succ.castSucc - θ i.castSucc.castSucc = chain.corner i.castSucc := steps i.castSucc
    have finish : θ i.succ.castSucc + chain.corner i.succ = θ i.succ.succ := by
      have := steps i.succ
      linarith
    rw [← finish]
    exact outward_motion_point motion _ _ _ _ _ _ _
      (chain.radius_pos _) (chain.radius_pos _) (chain.radius_pos _)
      (by rw [delta]; exact chain.corner_pos _) (by rw [delta]; exact chain.corner_lt_pi _)
      (chain.corner_pos _) (chain.corner_lt_pi _) previous shared rfl (chain.outward i)
  have third := next 0 first second
  have fourth := next 1 second third
  intro i
  fin_cases i
  · exact first
  · exact second
  · exact third
  · exact fourth

end ThreeTriangleChain

namespace ThreeTriangleChain

/-- Two aligned rays determine every ray in the prescribed clockwise frame. -/
theorem polar_motion_down (chain : ThreeTriangleChain) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (θ : Fin 4 → ℝ) (steps : ∀ i : Fin 3, θ i.castSucc - θ i.succ = chain.corner i)
    (first : motion (chain.ray 0) - motion chain.center = chain.radius 0 • direction (θ 0))
    (second : motion (chain.ray 1) - motion chain.center = chain.radius 1 • direction (θ 1)) :
    ∀ i, motion (chain.ray i) - motion chain.center = chain.radius i • direction (θ i) := by
  have next (i : Fin 2)
      (previous : motion (chain.ray i.castSucc.castSucc) - motion chain.center =
        chain.radius i.castSucc.castSucc • direction (θ i.castSucc.castSucc))
      (shared : motion (chain.ray i.succ.castSucc) - motion chain.center =
        chain.radius i.succ.castSucc • direction (θ i.succ.castSucc)) :
      motion (chain.ray i.succ.succ) - motion chain.center =
        chain.radius i.succ.succ • direction (θ i.succ.succ) := by
    have delta : θ i.castSucc.castSucc - θ i.succ.castSucc = chain.corner i.castSucc := steps i.castSucc
    have finish : θ i.succ.castSucc - chain.corner i.succ = θ i.succ.succ := by
      have := steps i.succ
      linarith
    rw [← finish]
    exact outward_motion_point_down motion _ _ _ _ _ _ _
      (chain.radius_pos _) (chain.radius_pos _) (chain.radius_pos _)
      (by rw [delta]; exact chain.corner_pos _) (by rw [delta]; exact chain.corner_lt_pi _)
      (chain.corner_pos _) (chain.corner_lt_pi _) previous shared rfl (chain.outward i)
  have third := next 0 first second
  have fourth := next 1 second third
  intro i
  fin_cases i
  · exact first
  · exact second
  · exact third
  · exact fourth

end ThreeTriangleChain

namespace FourTriangleChain

/-- Two aligned rays determine every ray in the prescribed counterclockwise frame. -/
theorem polar_motion_up (chain : FourTriangleChain) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (θ : Fin 5 → ℝ) (steps : ∀ i : Fin 4, θ i.succ - θ i.castSucc = chain.corner i)
    (first : motion (chain.ray 0) - motion chain.center = chain.radius 0 • direction (θ 0))
    (second : motion (chain.ray 1) - motion chain.center = chain.radius 1 • direction (θ 1)) :
    ∀ i, motion (chain.ray i) - motion chain.center = chain.radius i • direction (θ i) := by
  have next (i : Fin 3)
      (previous : motion (chain.ray i.castSucc.castSucc) - motion chain.center =
        chain.radius i.castSucc.castSucc • direction (θ i.castSucc.castSucc))
      (shared : motion (chain.ray i.succ.castSucc) - motion chain.center =
        chain.radius i.succ.castSucc • direction (θ i.succ.castSucc)) :
      motion (chain.ray i.succ.succ) - motion chain.center =
        chain.radius i.succ.succ • direction (θ i.succ.succ) := by
    have delta : θ i.succ.castSucc - θ i.castSucc.castSucc = chain.corner i.castSucc := steps i.castSucc
    have finish : θ i.succ.castSucc + chain.corner i.succ = θ i.succ.succ := by
      have := steps i.succ
      linarith
    rw [← finish]
    exact outward_motion_point motion _ _ _ _ _ _ _
      (chain.radius_pos _) (chain.radius_pos _) (chain.radius_pos _)
      (by rw [delta]; exact chain.corner_pos _) (by rw [delta]; exact chain.corner_lt_pi _)
      (chain.corner_pos _) (chain.corner_lt_pi _) previous shared rfl (chain.outward i)
  have third := next 0 first second
  have fourth := next 1 second third
  have fifth := next 2 third fourth
  intro i
  fin_cases i
  · exact first
  · exact second
  · exact third
  · exact fourth
  · exact fifth

end FourTriangleChain

namespace FourTriangleChain

/-- Two aligned rays determine every ray in the prescribed clockwise frame. -/
theorem polar_motion_down (chain : FourTriangleChain) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (θ : Fin 5 → ℝ) (steps : ∀ i : Fin 4, θ i.castSucc - θ i.succ = chain.corner i)
    (first : motion (chain.ray 0) - motion chain.center = chain.radius 0 • direction (θ 0))
    (second : motion (chain.ray 1) - motion chain.center = chain.radius 1 • direction (θ 1)) :
    ∀ i, motion (chain.ray i) - motion chain.center = chain.radius i • direction (θ i) := by
  have next (i : Fin 3)
      (previous : motion (chain.ray i.castSucc.castSucc) - motion chain.center =
        chain.radius i.castSucc.castSucc • direction (θ i.castSucc.castSucc))
      (shared : motion (chain.ray i.succ.castSucc) - motion chain.center =
        chain.radius i.succ.castSucc • direction (θ i.succ.castSucc)) :
      motion (chain.ray i.succ.succ) - motion chain.center =
        chain.radius i.succ.succ • direction (θ i.succ.succ) := by
    have delta : θ i.castSucc.castSucc - θ i.succ.castSucc = chain.corner i.castSucc := steps i.castSucc
    have finish : θ i.succ.castSucc - chain.corner i.succ = θ i.succ.succ := by
      have := steps i.succ
      linarith
    rw [← finish]
    exact outward_motion_point_down motion _ _ _ _ _ _ _
      (chain.radius_pos _) (chain.radius_pos _) (chain.radius_pos _)
      (by rw [delta]; exact chain.corner_pos _) (by rw [delta]; exact chain.corner_lt_pi _)
      (chain.corner_pos _) (chain.corner_lt_pi _) previous shared rfl (chain.outward i)
  have third := next 0 first second
  have fourth := next 1 second third
  have fifth := next 2 third fourth
  intro i
  fin_cases i
  · exact first
  · exact second
  · exact third
  · exact fourth
  · exact fifth

end FourTriangleChain

end SixVertexUnfolding
