import SixVertexUnfolding.Geometry.TriangleWeights

/-! Strict comparison with the virtual intersection of two cut rays in the opposite-petal argument. -/

namespace SixVertexUnfolding

/-- Inside a triangle, the sum of distances to the base endpoints is strictly smaller than at the third vertex,
except at that third vertex itself. -/
theorem triangle_distance_sum_lt (a b c m : Plane)
    (apex_farther : dist a b < dist c a + dist c b)
    (contained : m ∈ convexHull ℝ ({a, b, c} : Set Plane)) (not_apex : m ≠ c) :
    dist m a + dist m b < dist c a + dist c b := by
  have reorder : ({a, b, c} : Set Plane) = {c, a, b} := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [reorder, convexHull_insert (Set.insert_nonempty a {b})] at contained
  obtain ⟨z, hz, y, hy, between⟩ := mem_convexJoin.mp contained
  have same : z = c := hz
  subst z
  obtain ⟨s, t, hs, ht, total, expression⟩ := between
  have t_pos : 0 < t := by
    apply lt_of_le_of_ne ht
    intro zero
    have s_one : s = 1 := by linarith
    apply not_apex
    rw [← expression, ← zero, s_one, one_smul, zero_smul, add_zero]
  let f := fun x : Plane => dist x a + dist x b
  have convex_f : ConvexOn ℝ Set.univ f := (convexOn_univ_dist a).add (convexOn_univ_dist b)
  have sublevel : Convex ℝ {x | f x ≤ dist a b} := by simpa using convex_f.convex_le (dist a b)
  have y_bound : f y ≤ dist a b := by
    apply convexHull_min _ sublevel hy
    intro x member
    rcases member with same | same
    · rw [same]
      simp [f]
    · change x = b at same
      rw [same]
      simp [f, dist_comm]
  have convex_bound := convex_f.2 (Set.mem_univ c) (Set.mem_univ y) hs ht total
  rw [expression] at convex_bound
  change f m ≤ s * f c + t * f y at convex_bound
  have balance := congrArg (fun z : ℝ => z * f c) total
  simp only [add_mul, one_mul] at balance
  have strict_product := mul_pos t_pos (sub_pos.mpr apex_farther)
  change 0 < t * (f c - dist a b) at strict_product
  change f m < f c
  nlinarith [mul_nonneg ht (sub_nonneg.mpr y_bound)]

end SixVertexUnfolding
