import SixVertexUnfolding.Geometry.VertexFanPointAngles
import SixVertexUnfolding.Geometry.VertexFigureSectors

/-! Distinct actual corner triangles meet away from the pole only along
their common original edge ray. The supporting sides prove this for every
fan size, rather than by enumerating a fixed four-sector model. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan

open Set

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  (fan : P.VertexFaceFan pole n)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

private theorem supporting_segment_endpoint (side : Space →ₗ[ℝ] ℝ) {a b x : Space}
    (negative : side a < 0) (nonpositive : side b ≤ 0) (zero : side x = 0)
    (member : x ∈ segment ℝ a b) : x = b := by
  obtain ⟨u, v, hu, hv, total, combination⟩ := member
  have values := congrArg side combination
  simp only [map_add, map_smul, smul_eq_mul, zero] at values
  have first : u * side a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu negative.le
  have second : v * side b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv nonpositive
  have uz : u = 0 := by nlinarith
  have vz : v = 1 := by linarith
  simpa only [uz, vz, zero_smul, one_smul, zero_add] using combination.symm

include small_faces in
/-- Different supported sides share only their common cyclic endpoint. -/
theorem common_side_point (figure : P.VertexFigure pole) (i j : Fin n) (different : i ≠ j)
    {x : Space} (first : x ∈ segment ℝ (fan.ray figure i) (fan.ray figure (i + 1)))
    (second : x ∈ segment ℝ (fan.ray figure j) (fan.ray figure (j + 1))) :
    (j = i + 1 ∧ x = fan.ray figure (i + 1)) ∨
    (i = j + 1 ∧ x = fan.ray figure i) := by
  obtain ⟨side, _, left, right, bounds, strict⟩ := fan.ray_side_exists figure small_faces i
  have zero : side x = 0 := by
    obtain ⟨u, v, _, _, _, combination⟩ := first
    rw [← combination, map_add, map_smul, map_smul, left, right]
    simp
  by_cases next : j = i + 1
  · have not_left : j + 1 ≠ i := by
      intro back
      -- A two-step return is impossible in the cyclic neighbor list.
      have lower : 3 ≤ n := by
        have count := Nat.card_congr fan.order
        have degree := P.edgeGraph_min_degree pole
        rw [Nat.card_fin, Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at count
        omega
      have two : (0 : Fin n) = 1 + 1 := add_left_cancel
        (show i + 0 = i + (1 + 1) by rw [add_zero, ← add_assoc, ← next, back])
      have values := congrArg Fin.val two
      change 0 = (1 % n + 1 % n) % n at values
      simp only [Nat.mod_eq_of_lt (show 1 < n by omega),
        show 1 + 1 = 2 from rfl, Nat.mod_eq_of_lt (show 2 < n by omega)] at values
      omega
    have not_right : j + 1 ≠ i + 1 := fun equal => different (add_right_cancel equal).symm
    have endpoint := supporting_segment_endpoint side (strict _ not_left not_right)
      (bounds j) zero (by rwa [segment_symm])
    exact Or.inl ⟨next, by simpa only [next] using endpoint⟩
  · have endpoint := supporting_segment_endpoint side (strict j different.symm next)
      (bounds (j + 1)) zero second
    have equal : i = j + 1 := by
      by_contra distinct
      have not_right : j + 1 ≠ i + 1 := fun equal => different (add_right_cancel equal).symm
      have negative := strict (j + 1) (fun equal => distinct equal.symm) not_right
      rw [← endpoint, zero] at negative
      exact (lt_irrefl 0) negative
    exact Or.inr ⟨equal, by simpa only [← equal] using endpoint⟩

include small_faces in
/-- Two distinct actual sectors meet only on a shared original edge ray. -/
theorem common_sector_ray (i j : Fin n) (different : i ≠ j)
    (x : Space) (first : x ∈ fan.triangle i) (second : x ∈ fan.triangle j)
    (nonpole : x ≠ pole) :
    (j = i + 1 ∧ ∃ t : ℝ, 0 < t ∧ x = t • ((fan.neighbor (i + 1) : Space) - pole) + pole) ∨
    (i = j + 1 ∧ ∃ t : ℝ, 0 < t ∧ x = t • ((fan.neighbor i : Space) - pole) + pole) := by
  obtain ⟨normal, strict⟩ := P.vertex_strict_support pole.property
  let figure : P.VertexFigure pole := ⟨normal, strict⟩
  have gaps (k : Fin n) : 0 < figure.gap (fan.neighbor k) :=
    figure.gap_pos (fan.neighbor k).property (fan.neighbor_ne_pole k)
  have projected (k : Fin n) (hx : x ∈ fan.triangle k) :
      figure.direction x ∈ segment ℝ (fan.ray figure k) (fan.ray figure (k + 1)) :=
    figure.sector_direction_in_side _ _ (gaps k) (gaps (k + 1)) x hx nonpole
  have positive := figure.sector_gap_positive _ _ (gaps i) (gaps (i + 1)) x first nonpole
  rcases fan.common_side_point small_faces figure i j different
      (projected i first) (projected j second) with h | h
  · exact Or.inl ⟨h.1, figure.equal_direction_ray _ x (gaps (i + 1)) positive h.2⟩
  · exact Or.inr ⟨h.1, figure.equal_direction_ray _ x (gaps i) positive h.2⟩

/-- A positive radial rescaling does not change the sector offset. -/
theorem offset_on_ray (i j : Fin n) (t : ℝ) (positive : 0 < t) :
    fan.offset i (t • ((fan.neighbor j : Space) - pole) + pole) =
      EuclideanGeometry.angle (fan.neighbor i : Space) pole (fan.neighbor j) := by
  unfold offset EuclideanGeometry.angle
  simp only [vsub_eq_sub, add_sub_cancel_right]
  exact InnerProductGeometry.angle_smul_right_of_pos _ _ positive

include small_faces in
/-- Adjacent offsets are the full preceding angle and zero in the next sector. -/
theorem adjacent_sector_offsets (i : Fin n) (x : Space)
    (first : x ∈ fan.triangle i) (second : x ∈ fan.triangle (i + 1)) (nonpole : x ≠ pole) :
    fan.offset i x = fan.sectorAngle i ∧ fan.offset (i + 1) x = 0 := by
  have distinct : i ≠ i + 1 := fun equal => fan.successive_distinct i (congrArg fan.neighbor equal)
  rcases fan.common_sector_ray small_faces i (i + 1) distinct x first second nonpole with h | h
  · obtain ⟨t, positive, rfl⟩ := h.2
    rw [fan.offset_on_ray i (i + 1) t positive, fan.offset_on_ray (i + 1) (i + 1) t positive]
    exact ⟨rfl, EuclideanGeometry.angle_self_of_ne (fan.neighbor_ne_pole (i + 1))⟩
  · have lower : 3 ≤ n := by
      have count := Nat.card_congr fan.order
      have degree := P.edgeGraph_min_degree pole
      rw [Nat.card_fin, Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at count
      omega
    have two : (0 : Fin n) = 1 + 1 := add_left_cancel
      (show i + 0 = i + (1 + 1) by rw [add_zero, ← add_assoc, ← h.1])
    have values := congrArg Fin.val two
    change 0 = (1 % n + 1 % n) % n at values
    simp only [Nat.mod_eq_of_lt (show 1 < n by omega),
      show 1 + 1 = 2 from rfl, Nat.mod_eq_of_lt (show 2 < n by omega)] at values
    omega

end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan
