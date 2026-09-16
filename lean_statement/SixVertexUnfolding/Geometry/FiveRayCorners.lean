import SixVertexUnfolding.Geometry.FiveRayFan

/-! Each ray of the supported pentagon is a genuine convex corner.
Adding its adjacent supporting heights strictly exposes that corner. -/

namespace SixVertexUnfolding.FiveRayFan

open Set

/-- The sum of the two incident supporting functions exposes one corner. -/
noncomputable def cornerHeight (fan : FiveRayFan) (i : Fin 5) : Space →ₗ[ℝ] ℝ :=
  fan.side (i - 1) + fan.side i

theorem cornerHeight_self (fan : FiveRayFan) (i : Fin 5) :
    fan.cornerHeight i (fan.ray i) = 0 := by
  have previous : fan.side (i - 1) (fan.ray i) = 0 := by
    simpa only [sub_add_cancel] using fan.side_right (i - 1)
  simp only [cornerHeight, LinearMap.add_apply, previous, fan.side_left, add_zero]

/-- Every other corner has strictly lower exposing height. -/
theorem cornerHeight_strict (fan : FiveRayFan) (i j : Fin 5) (different : j ≠ i) :
    fan.cornerHeight i (fan.ray j) < 0 := by
  change fan.side (i - 1) (fan.ray j) + fan.side i (fan.ray j) < 0
  by_cases previous : j = i - 1
  · have not_next : j ≠ i + 1 := by
      rw [previous]
      exact (by decide : ∀ i : Fin 5, i - 1 ≠ i + 1) i
    exact add_neg_of_nonpos_of_neg (fan.side_bound (i - 1) j) (fan.side_strict i j different not_next)
  · exact add_neg_of_neg_of_nonpos
      (fan.side_strict (i - 1) j previous (by simpa only [sub_add_cancel] using different))
      (fan.side_bound i j)

/-- None of the five corners lies in the convex hull of the other four. -/
theorem corner_not_mem_other_hull (fan : FiveRayFan) (i : Fin 5) :
    fan.ray i ∉ convexHull ℝ (range fan.ray \ {fan.ray i}) := by
  have below : range fan.ray \ {fan.ray i} ⊆ (fan.cornerHeight i) ⁻¹' Iio 0 := by
    rintro x ⟨⟨j, rfl⟩, different⟩
    exact fan.cornerHeight_strict i j (fun same => different (by rw [same]; rfl))
  have hull_below := convexHull_min below ((convex_Iio (0 : ℝ)).linear_preimage (fan.cornerHeight i))
  intro member
  have impossible := hull_below member
  change fan.cornerHeight i (fan.ray i) < 0 at impossible
  rw [fan.cornerHeight_self] at impossible
  exact lt_irrefl _ impossible

end SixVertexUnfolding.FiveRayFan
