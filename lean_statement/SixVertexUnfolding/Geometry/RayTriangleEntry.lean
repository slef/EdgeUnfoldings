import SixVertexUnfolding.Geometry.TriangleWeights

/-! A ray entering a triangle from behind its near vertex must meet one of the two near edges. -/

namespace SixVertexUnfolding

private theorem ray_meets_near_edge (a b p x : Plane) (β γ u v z : ℝ)
    (beta_pos : 0 < β) (near : β + γ ≤ 1)
    (at_a : a = β • b + γ • p)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (total : u + v + z = 1)
    (at_x : x = u • a + v • b + z • p) (side : γ * v ≤ β * z) :
    ∃ k : ℝ, 0 < k ∧ k ≤ 1 ∧ k • x ∈ segment ℝ a p := by
  let D := β + v * (1 - β - γ)
  have slack : 0 ≤ 1 - β - γ := by linarith
  have D_pos : 0 < D := by dsimp [D]; positivity
  have D_ne : D ≠ 0 := D_pos.ne'
  refine ⟨β / D, div_pos beta_pos D_pos, (div_le_one D_pos).mpr ?_, ?_⟩
  · dsimp [D]; nlinarith [mul_nonneg hv slack]
  · refine ⟨(u * β + v) / D, (β * z - γ * v) / D,
      div_nonneg (by positivity) D_pos.le, div_nonneg (sub_nonneg.mpr side) D_pos.le, ?_, ?_⟩
    · rw [← add_div]
      apply (div_eq_one_iff_eq D_ne).mpr
      dsimp [D]
      nlinarith
    · rw [at_x, at_a]
      rw [show z = 1 - u - v by linarith]
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      dsimp [D]
      field_simp
      ring

/-- If the near vertex lies inside the radial triangle, every point of the far triangle is reached through a near edge. -/
theorem ray_enters_triangle_at_near_edges (a b p x : Plane) (β γ : ℝ)
    (beta_pos : 0 < β) (gamma_pos : 0 < γ) (near : β + γ ≤ 1)
    (at_a : a = β • b + γ • p)
    (member : x ∈ convexHull ℝ ({a, b, p} : Set Plane)) :
    ∃ k : ℝ, 0 < k ∧ k ≤ 1 ∧ k • x ∈ segment ℝ a b ∪ segment ℝ a p := by
  obtain ⟨u, v, z, hu, hv, hz, total, at_x⟩ := triangle_weights a b p x member
  by_cases side : γ * v ≤ β * z
  · obtain ⟨k, positive, upper, hit⟩ := ray_meets_near_edge a b p x β γ u v z
      beta_pos near at_a hu hv total at_x.symm side
    exact ⟨k, positive, upper, Or.inr hit⟩
  · have at_a' : a = γ • p + β • b := by rw [at_a]; module
    have at_x' : x = u • a + z • p + v • b := by rw [← at_x]; module
    obtain ⟨k, positive, upper, hit⟩ := ray_meets_near_edge a p b x γ β u z v
      gamma_pos (by linarith) at_a' hu hz (by linarith) at_x' (by linarith)
    exact ⟨k, positive, upper, Or.inl hit⟩

/-- Closed finite contact reaches a near edge before reaching the original contact point. -/
theorem finite_ray_contact_reaches_near_edge (a b p c x : Plane)
    (near : a ∈ convexHull ℝ ({0, b, p} : Set Plane))
    (off_b : a ∉ segment ℝ 0 b) (off_p : a ∉ segment ℝ 0 p)
    (member : x ∈ convexHull ℝ ({a, b, p} : Set Plane))
    (contact : x ∈ segment ℝ 0 c) (nonzero : x ≠ 0) :
    ∃ y : Plane, y ≠ 0 ∧ y ∈ segment ℝ 0 c ∧ y ∈ segment ℝ a b ∪ segment ℝ a p := by
  obtain ⟨α, β, γ, ha, hb, hg, total, position⟩ := triangle_weights 0 b p a near
  have beta_pos : 0 < β := by
    apply lt_of_le_of_ne hb
    intro zero
    have vanish : β = 0 := zero.symm
    apply off_p
    refine ⟨α, γ, ha, hg, by linarith, ?_⟩
    simpa only [vanish, zero_smul, add_zero] using position
  have gamma_pos : 0 < γ := by
    apply lt_of_le_of_ne hg
    intro zero
    have vanish : γ = 0 := zero.symm
    apply off_b
    refine ⟨α, β, ha, hb, by linarith, ?_⟩
    simpa only [vanish, zero_smul, add_zero] using position
  have at_a : a = β • b + γ • p := by simpa only [smul_zero, zero_add] using position.symm
  obtain ⟨k, positive, upper, hit⟩ := ray_enters_triangle_at_near_edges a b p x β γ
    beta_pos gamma_pos (by linarith) at_a member
  refine ⟨k • x, smul_ne_zero positive.ne' nonzero, ?_, hit⟩
  apply (convex_segment 0 c).segment_subset (left_mem_segment ℝ _ _) contact
  exact ⟨1 - k, k, by linarith, positive.le, by ring, by simp⟩

/-- If the hinge edge misses the slit, contact must occur on the copied cut edge. -/
theorem finite_ray_contact_reaches_cut_edge (a b p c x : Plane)
    (near : a ∈ convexHull ℝ ({0, b, p} : Set Plane))
    (off_b : a ∉ segment ℝ 0 b) (off_p : a ∉ segment ℝ 0 p)
    (member : x ∈ convexHull ℝ ({a, b, p} : Set Plane))
    (contact : x ∈ segment ℝ 0 c) (nonzero : x ≠ 0)
    (hinge_clear : Disjoint (segment ℝ a b) (segment ℝ 0 c)) :
    ∃ y : Plane, y ≠ 0 ∧ y ∈ segment ℝ 0 c ∧ y ∈ segment ℝ a p := by
  obtain ⟨y, nonzero_y, on_slit, on_edge⟩ := finite_ray_contact_reaches_near_edge a b p c x
    near off_b off_p member contact nonzero
  rcases on_edge with on_hinge | on_cut
  · exact False.elim (Set.disjoint_left.mp hinge_clear on_hinge on_slit)
  · exact ⟨y, nonzero_y, on_slit, on_cut⟩

end SixVertexUnfolding
