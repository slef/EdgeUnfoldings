import SixVertexUnfolding.Geometry.PlacedFaces
import SixVertexUnfolding.Geometry.HingeSideOrder

/-! Nonoverlapping whole faces joined along an edge necessarily lie on opposite
sides of that edge. This recovers the outward condition from a star embedding. -/

namespace SixVertexUnfolding

/-- A nonconstant separating height, constant along a hinge, certifies opposite sides. -/
theorem oppositeHingeSides_of_separator (a b x y : Plane) (ab : a ≠ b)
    (height : Plane →L[ℝ] ℝ) (onto : Function.Surjective height)
    (level : ℝ) (ha : height a = level) (hb : height b = level)
    (hx : height x ≤ level) (hy : level ≤ height y) : OppositeHingeSides a b x y := by
  let axis := NormedSpace.normalize (b - a)
  let n := (InnerProductSpace.toDual ℝ Plane).symm height
  have eval (z : Plane) : inner ℝ n z = height z := InnerProductSpace.toDual_symm_apply
  have n_ne : n ≠ 0 := by
    intro zero
    obtain ⟨z, hz⟩ := onto 1
    have h := eval z
    rw [zero, inner_zero_left, hz] at h
    norm_num at h
  have unit : ‖axis‖ = 1 := NormedSpace.norm_normalize (sub_ne_zero.mpr ab.symm)
  have axis_ne : axis ≠ 0 := by intro h; simp [h] at unit
  have n_orthogonal : inner ℝ axis n = 0 := by
    rw [real_inner_comm]
    change inner ℝ n (‖b - a‖⁻¹ • (b - a)) = 0
    rw [inner_smul_right, eval, map_sub, hb, ha, sub_self, mul_zero]
  have orthogonal (z : Plane) : inner ℝ axis (hingeSideVector a b z) = 0 :=
    hingeRemainder_orthogonal unit (z - a)
  obtain ⟨s, hs⟩ := perpendicular_multiple axis n (hingeSideVector a b x)
    axis_ne n_ne n_orthogonal (orthogonal x)
  obtain ⟨t, ht⟩ := perpendicular_multiple axis n (hingeSideVector a b y)
    axis_ne n_ne n_orthogonal (orthogonal y)
  have n_axis : inner ℝ n axis = 0 := by rw [real_inner_comm]; exact n_orthogonal
  have height_side (z : Plane) : inner ℝ n (hingeSideVector a b z) = height z - level := by
    change inner ℝ n ((z - a) - inner ℝ axis (z - a) • axis) = _
    rw [inner_sub_right, inner_smul_right, n_axis,
      mul_zero, sub_zero, eval, map_sub, ha]
  have left := height_side x
  have right := height_side y
  rw [hs, inner_smul_right, real_inner_self_eq_norm_sq] at left
  rw [ht, inner_smul_right, real_inner_self_eq_norm_sq] at right
  have positive : 0 < ‖n‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr n_ne)
  have s_nonpos : s ≤ 0 := by nlinarith
  have t_nonneg : 0 ≤ t := by nlinarith
  change inner ℝ (hingeSideVector a b x) (hingeSideVector a b y) ≤ 0
  rw [hs, ht, real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
  exact mul_nonpos_of_nonpos_of_nonneg s_nonpos (mul_nonneg t_nonneg positive.le)

namespace ConvexPolyhedron.Face

/-- A nonoverlapping joined pair has the outward-side condition at every point. -/
theorem opposite_sides_of_nonoverlap {P : ConvexPolyhedron} (F G : P.Face)
    (left right : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (left x) (left y) = dist x y)
    (right_rigid : ∀ x ∈ G.val, ∀ y ∈ G.val, dist (right x) (right y) = dist x y)
    (joined : Set.EqOn left right (F.val ∩ G.val))
    (nonoverlap : Disjoint (interior (left '' F.val)) (interior (right '' G.val)))
    (a : Space) (ha : a ∈ (F.val ∩ G.val) ∩ (P.vertices : Set Space))
    (b : Space) (hb : b ∈ (F.val ∩ G.val) ∩ (P.vertices : Set Space)) (ab : a ≠ b)
    (x : Space) (hx : x ∈ F.val) (y : Space) (hy : y ∈ G.val) :
    OppositeHingeSides (left a) (left b) (left x) (right y) := by
  obtain ⟨height, onto, level, upper, lower⟩ :=
    (F.nonoverlap_iff_vertex_separator G left right left_rigid right_rigid).mp nonoverlap
  have at_hinge (z : Space) (hz : z ∈ (F.val ∩ G.val) ∩ (P.vertices : Set Space)) :
      height (left z) = level := by
    apply le_antisymm (upper z ⟨hz.1.1, hz.2⟩)
    rw [joined hz.1]
    exact lower z ⟨hz.1.2, hz.2⟩
  have distinct : left a ≠ left b := by
    intro same
    have distance := left_rigid a ha.1.1 b hb.1.1
    rw [same, dist_self] at distance
    exact ab (dist_eq_zero.mp distance.symm)
  exact oppositeHingeSides_of_separator (left a) (left b) (left x) (right y) distinct
    height onto level (at_hinge a ha) (at_hinge b hb)
    (F.upper_bound_of_vertices left height level upper x hx)
    (G.lower_bound_of_vertices right height level lower y hy)

end ConvexPolyhedron.Face
end SixVertexUnfolding
