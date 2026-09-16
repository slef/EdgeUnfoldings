import SixVertexUnfolding.Definitions

/-! Every nonzero point on a closed segment from the origin has the endpoint's angular direction. -/

namespace SixVertexUnfolding

theorem angle_eq_of_mem_radial_segment (a b x : Plane) (member : x ∈ segment ℝ 0 b) (nonzero : x ≠ 0) :
    EuclideanGeometry.angle a 0 x = EuclideanGeometry.angle a 0 b := by
  obtain ⟨s, t, hs, ht, total, expression⟩ := member
  simp only [smul_zero, zero_add] at expression
  have positive : 0 < t := by
    apply lt_of_le_of_ne ht
    intro zero
    apply nonzero
    rw [← expression, ← zero, zero_smul]
  rw [← expression]
  change InnerProductGeometry.angle (a - 0) (t • b - 0) = InnerProductGeometry.angle (a - 0) (b - 0)
  simp only [sub_zero, InnerProductGeometry.angle_smul_right_of_pos _ _ positive]

end SixVertexUnfolding
