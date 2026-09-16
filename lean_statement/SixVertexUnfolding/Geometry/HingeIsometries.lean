import SixVertexUnfolding.Geometry.HingeUniqueness

/-! Hinge-side conditions and triangle placements are invariant under planar rigid motions. -/

namespace SixVertexUnfolding

theorem normalize_linearIsometry (turn : Plane ≃ₗᵢ[ℝ] Plane) (x : Plane) :
    NormedSpace.normalize (turn x) = turn (NormedSpace.normalize x) := by
  simp [NormedSpace.normalize]

theorem hingeRemainder_linearIsometry (turn : Plane ≃ₗᵢ[ℝ] Plane) (axis x : Plane) :
    hingeRemainder (turn axis) (turn x) = turn (hingeRemainder axis x) := by
  simp [hingeRemainder]

/-- A rigid motion carries the perpendicular hinge vector by its orthogonal linear part. -/
theorem hingeSideVector_motion (motion : Plane ≃ᵃⁱ[ℝ] Plane) (a b x : Plane) :
    hingeSideVector (motion a) (motion b) (motion x) =
      motion.linearIsometryEquiv (hingeSideVector a b x) := by
  have difference (p q : Plane) : motion p - motion q = motion.linearIsometryEquiv (p - q) :=
    (motion.map_vsub p q).symm
  simp only [hingeSideVector, difference, normalize_linearIsometry, hingeRemainder_linearIsometry]

/-- Opposite-side flattening is independent of the chosen rigid planar coordinate frame. -/
theorem oppositeHingeSides_motion (motion : Plane ≃ᵃⁱ[ℝ] Plane) (a b x y : Plane) :
    OppositeHingeSides (motion a) (motion b) (motion x) (motion y) ↔ OppositeHingeSides a b x y := by
  simp only [OppositeHingeSides, hingeSideVector_motion, motion.linearIsometryEquiv.inner_map_map]

/-- Three matching sides admit a rigid planar motion taking all three corners to their targets. -/
theorem exists_plane_motion_triangle (a b c A B C : Plane) (ab : A ≠ B)
    (AB : dist a b = dist A B) (AC : dist a c = dist A C) (BC : dist b c = dist B C) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, motion a = A ∧ motion b = B ∧ motion c = C := by
  obtain ⟨align, at_a, at_b⟩ := exists_plane_motion a b A B AB
  obtain ⟨flip, fixed_a, fixed_b, side⟩ := exists_opposite_hinge_motion A B (2 • A - C) (align c) ab
  let motion := align.trans flip
  have first : motion a = A := by change flip (align a) = A; rw [at_a, fixed_a]
  have second : motion b = B := by change flip (align b) = B; rw [at_b, fixed_b]
  refine ⟨motion, first, second, ?_⟩
  apply point_eq_of_hinge_distances A B (motion c) C ab
  · rw [← first, motion.dist_map, AC, first]
  · rw [← second, motion.dist_map, BC, second]
  · change inner ℝ (hingeSideVector A B (2 • A - C)) (hingeSideVector A B (motion c)) ≤ 0 at side
    rw [hingeSideVector_point_reflection, inner_neg_left] at side
    rw [real_inner_comm]
    linarith

end SixVertexUnfolding
