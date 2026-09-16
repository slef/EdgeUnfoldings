import SixVertexUnfolding.Geometry.BisectorKites
import SixVertexUnfolding.Geometry.HingeIsometries

/-! Two distinct points with the same distances to a nontrivial base
exhaust the possibilities for those two distances in the plane.
-/

namespace SixVertexUnfolding

/-- A planar base and two distances determine at most two possible source copies. -/
theorem point_eq_or_eq_of_base_distances (u v p q x : Plane)
    (base : u ≠ v) (different : p ≠ q)
    (pq_left : dist p u = dist q u) (pq_right : dist p v = dist q v)
    (xp_left : dist x u = dist p u) (xp_right : dist x v = dist p v) :
    x = p ∨ x = q := by
  by_contra neither
  push Not at neither
  have pq := bisector_sites_opposite p q u v different base pq_left pq_right
  have px := bisector_sites_opposite p x u v (Ne.symm neither.1) base xp_left.symm xp_right.symm
  have qx := bisector_sites_opposite q x u v (Ne.symm neither.2) base
    (pq_left.symm.trans xp_left.symm) (pq_right.symm.trans xp_right.symm)
  rcases mul_neg_iff.mp pq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · have hx : det (v - u) (x - u) < 0 := (mul_neg_iff.mp px).resolve_right (by
      rintro ⟨bad, _⟩
      linarith)
      |>.2
    exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos hq.le hx.le)) qx
  · have hx : 0 < det (v - u) (x - u) := (mul_neg_iff.mp px).resolve_left (by
      rintro ⟨bad, _⟩
      linarith)
      |>.2
    exact (not_lt_of_ge (mul_nonneg hq.le hx.le)) qx

/-- A base and its two source copies move together once their distances
match those of a second such configuration. -/
theorem exists_bisector_motion (l r p q L R P Q : Plane)
    (base : L ≠ R) (old_sources : p ≠ q) (new_sources : P ≠ Q)
    (base_length : dist l r = dist L R)
    (left_length : dist p l = dist P L) (right_length : dist p r = dist P R)
    (old_left : dist p l = dist q l) (old_right : dist p r = dist q r)
    (new_left : dist P L = dist Q L) (new_right : dist P R = dist Q R) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane,
      motion l = L ∧ motion r = R ∧ motion p = P ∧ motion q = Q := by
  obtain ⟨motion, at_l, at_r, at_p⟩ := exists_plane_motion_triangle l r p L R P base base_length
    (by simpa only [dist_comm] using left_length) (by simpa only [dist_comm] using right_length)
  refine ⟨motion, at_l, at_r, at_p, ?_⟩
  have left : dist (motion q) L = dist P L := by
    rw [← at_l, motion.dist_map, ← old_left, left_length, at_l]
  have right : dist (motion q) R = dist P R := by
    rw [← at_r, motion.dist_map, ← old_right, right_length, at_r]
  rcases point_eq_or_eq_of_base_distances L R P Q (motion q) base new_sources
    new_left new_right left right with same | desired
  · exact (old_sources (motion.injective (at_p.trans same.symm))).elim
  · exact desired

/-- Matching source distances at the left endpoint and one nonzero base
parameter forces matching distances at the right endpoint. -/
theorem right_distance_eq_of_sample (p l r P L R : Plane) {t : ℝ} (nonzero : t ≠ 0)
    (base : dist l r = dist L R) (left : dist p l = dist P L)
    (sample : dist p (AffineMap.lineMap l r t) = dist P (AffineMap.lineMap L R t)) :
    dist p r = dist P R := by
  have old := squared_distance_lineMap p l r t
  have new := squared_distance_lineMap P L R t
  rw [base, left, sample] at old
  have product : t * (dist p r ^ 2 - dist P R ^ 2) = 0 := by nlinarith
  have squares : dist p r ^ 2 = dist P R ^ 2 :=
    sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left nonzero)
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp squares

end SixVertexUnfolding
