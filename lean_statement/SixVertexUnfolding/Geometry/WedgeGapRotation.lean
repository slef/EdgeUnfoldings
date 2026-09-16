import SixVertexUnfolding.Geometry.PolarRotations
import SixVertexUnfolding.Geometry.CircularGapData

/-! The incoming gap fits between the outward-facing arms of any other
circular gap. Full-turn shifts are handled at the level of actual regions.
-/

namespace SixVertexUnfolding.Wedge

open Real Set

/-- In the outgoing gap's coordinate frame, the incoming wedge has precisely
the arm inequalities required by the checked rotate-and-move step. -/
theorem rotate_from_disjoint_gap (d ω α β γ δ : ℝ)
    (separated : (β ≤ γ ∧ δ ≤ α + 2 * π) ∨ (δ ≤ α ∧ β ≤ γ + 2 * π)) :
    ∃ turn : Plane ≃ₗᵢ[ℝ] Plane,
      (∀ φ, turn (direction φ) = direction (φ - (γ + δ) / 2)) ∧
      ∃ lower upper : ℝ,
        (δ - γ) / 2 ≤ lower ∧ upper ≤ 2 * π - (δ - γ) / 2 ∧
        turn '' polarRegion d ω α β = polarRegion d ω lower upper := by
  obtain ⟨turn, directions⟩ := exists_direction_rotation (-((γ + δ) / 2))
  have rotates (φ : ℝ) : turn (direction φ) = direction (φ - (γ + δ) / 2) := by
    simpa only [sub_eq_add_neg] using directions φ
  refine ⟨turn, rotates, ?_⟩
  have image := polarRegion_image_rotation turn (-((γ + δ) / 2)) directions d ω α β
  simp only [← sub_eq_add_neg] at image
  rcases separated with before | after
  · refine ⟨α - (γ + δ) / 2 + 2 * π, β - (γ + δ) / 2 + 2 * π,
      by linarith [before.2], by linarith [before.1], ?_⟩
    rw [polarRegion_add_two_pi]
    exact image
  · exact ⟨α - (γ + δ) / 2, β - (γ + δ) / 2,
      by linarith [after.1], by linarith [after.2], image⟩

/-- The finite circular source order supplies the separation hypothesis;
it need not be imposed independently at a junction. -/
theorem rotate_between_circular_gaps {n : ℕ} (θ : Fin n → ℝ) (increasing : StrictMono θ)
    (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π) (first last : Fin n)
    (at_first : first.val = 0) (at_last : last.val + 1 = n)
    {α β γ δ : ℝ} (incoming : IsCircularGap θ first last α β)
    (outgoing : IsCircularGap θ first last γ δ)
    (distinct : (α + β) / 2 ≠ (γ + δ) / 2) (d ω : ℝ) :
    ∃ turn : Plane ≃ₗᵢ[ℝ] Plane,
      (∀ φ, turn (direction φ) = direction (φ - (γ + δ) / 2)) ∧
      ∃ lower upper : ℝ,
        (δ - γ) / 2 ≤ lower ∧ upper ≤ 2 * π - (δ - γ) / 2 ∧
        turn '' polarRegion d ω α β = polarRegion d ω lower upper := by
  apply rotate_from_disjoint_gap
  rcases lt_or_gt_of_ne distinct with before | after
  · exact Or.inl (circular_gaps_separated θ increasing bounds first last at_first at_last
      incoming outgoing before)
  · exact Or.inr (circular_gaps_separated θ increasing bounds first last at_first at_last
      outgoing incoming after)

end SixVertexUnfolding.Wedge
