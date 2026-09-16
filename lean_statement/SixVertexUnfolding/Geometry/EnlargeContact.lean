import SixVertexUnfolding.Geometry.SupportingContacts

/-! Tilting a supporting plane adds a vertex unless its contacts already span a facet. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Orient a spare tangent direction toward at least one original vertex. -/
theorem forward_tilt_direction (P : ConvexPolyhedron) (x : Space)
    (D : Submodule ℝ Space) (r : Space)
    (small : Module.finrank ℝ D ≤ 1) (nonzero : r ≠ 0) :
    ∃ q : Space, q ∈ Dᗮ ∧ inner ℝ r q = 0 ∧
      ∃ v ∈ P.vertices, 0 < inner ℝ q v - inner ℝ q x := by
  obtain ⟨q, q_nonzero, q_orthogonal, q_normal⟩ := exists_tilt_direction D r small nonzero
  obtain ⟨v, hv, different⟩ := P.exists_vertex_height_ne q x q_nonzero
  by_cases forward : inner ℝ q x < inner ℝ q v
  · exact ⟨q, q_orthogonal, q_normal, v, hv, sub_pos.mpr forward⟩
  · refine ⟨-q, (Dᗮ).neg_mem q_orthogonal, ?_, v, hv, ?_⟩
    · simp [q_normal]
    · simp only [inner_neg_left]
      exact sub_pos.mpr (neg_lt_neg (lt_of_le_of_ne (le_of_not_gt forward) different))

/-- Tilt in a specified tangent direction until the first new vertex makes contact. -/
theorem tilt_contact_in_direction (P : ConvexPolyhedron) (n x q : Space)
    (support : P.SupportsAt n x) (point : x ∈ P.body)
    (orthogonal : q ∈ (vectorSpan ℝ (P.contactVertices n x : Set Space))ᗮ)
    (forward : ∃ v ∈ P.vertices, 0 < inner ℝ q v - inner ℝ q x) :
    ∃ t : ℝ, 0 < t ∧ P.SupportsAt (n + t • q) x ∧
      P.contactVertices n x ⊂ P.contactVertices (n + t • q) x := by
  classical
  let f := fun v => inner ℝ n v - inner ℝ n x
  let g := fun v => inner ℝ q v - inner ℝ q x
  have supported : ∀ v ∈ P.vertices, f v ≤ 0 := by
    intro v hv
    exact sub_nonpos.mpr (support v (P.vertices_subset_body hv))
  have fixed : ∀ v ∈ P.vertices, f v = 0 → g v = 0 := by
    intro v hv contact
    have active : v ∈ P.contactVertices n x :=
      Finset.mem_filter.mpr ⟨hv, sub_eq_zero.mp contact⟩
    exact sub_eq_zero.mpr (P.tilt_fixes_contacts n x support point orthogonal active)
  obtain ⟨t, positive, tilted_bound, b, hb, b_strict, b_contact⟩ :=
    finite_support_tilt P.vertices f g supported fixed forward
  have height (v : Space) :
      inner ℝ (n + t • q) v - inner ℝ (n + t • q) x = f v + t * g v := by
    simp only [f, g, inner_add_left, inner_smul_left, conj_trivial]
    ring
  refine ⟨t, positive, P.supportsAt_of_vertex_bounds (n + t • q) x ?_, ?_⟩
  · intro v hv
    exact sub_nonpos.mp (by rw [height]; exact tilted_bound v hv)
  · apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro v hv
      obtain ⟨vertex, contact⟩ := Finset.mem_filter.mp hv
      have f_zero : f v = 0 := sub_eq_zero.mpr contact
      apply Finset.mem_filter.mpr
      refine ⟨vertex, sub_eq_zero.mp ?_⟩
      rw [height, f_zero, fixed v vertex f_zero]
      ring
    · intro equal_contacts
      have new_contact : b ∈ P.contactVertices (n + t • q) x := by
        apply Finset.mem_filter.mpr
        exact ⟨hb, sub_eq_zero.mp (by rw [height]; exact b_contact)⟩
      rw [← equal_contacts] at new_contact
      have old_contact : f b = 0 := sub_eq_zero.mpr (Finset.mem_filter.mp new_contact).2
      linarith

/-- A supporting contact of dimension zero or one can be enlarged strictly. -/
theorem enlarge_contact (P : ConvexPolyhedron) (n x : Space)
    (normal_nonzero : n ≠ 0) (support : P.SupportsAt n x) (point : x ∈ P.body)
    (small : affineDimension (P.contactVertices n x : Set Space) ≤ 1) :
    ∃ m : Space, m ≠ 0 ∧ P.SupportsAt m x ∧
      P.contactVertices n x ⊂ P.contactVertices m x := by
  classical
  let D := vectorSpan ℝ (P.contactVertices n x : Set Space)
  have small_span : Module.finrank ℝ D ≤ 1 := by
    change Module.finrank ℝ (affineSpan ℝ (P.contactVertices n x : Set Space)).direction ≤ 1 at small
    rw [direction_affineSpan] at small
    exact small

  obtain ⟨q, orthogonal, q_normal, forward⟩ :=
    P.forward_tilt_direction x D n small_span normal_nonzero
  obtain ⟨t, _, tilted_support, larger⟩ :=
    P.tilt_contact_in_direction n x q support point orthogonal forward
  have nonzero : n + t • q ≠ 0 := by
    intro zero
    have normal_height : inner ℝ n (n + t • q) = inner ℝ n n := by
      simp [inner_add_right, inner_smul_right, q_normal]
    rw [zero, inner_zero_right] at normal_height
    exact normal_nonzero (inner_self_eq_zero.mp normal_height.symm)
  exact ⟨n + t • q, nonzero, tilted_support, larger⟩

/-- The contact can also be enlarged while keeping a specified point strictly below the plane. -/
theorem enlarge_contact_avoiding (P : ConvexPolyhedron) (n x z : Space)
    (support : P.SupportsAt n x) (point : x ∈ P.body)
    (excluded : inner ℝ n z < inner ℝ n x)
    (small : affineDimension (P.contactVertices n x : Set Space) ≤ 1) :
    ∃ m : Space, m ≠ 0 ∧ P.SupportsAt m x ∧
      P.contactVertices n x ⊂ P.contactVertices m x ∧ inner ℝ m z < inner ℝ m x := by
  let D := vectorSpan ℝ (P.contactVertices n x : Set Space)
  have small_span : Module.finrank ℝ D ≤ 1 := by
    change Module.finrank ℝ (affineSpan ℝ (P.contactVertices n x : Set Space)).direction ≤ 1 at small
    rwa [direction_affineSpan] at small
  have different : z - x ≠ 0 := by
    intro equal
    have same := sub_eq_zero.mp equal
    exact (lt_irrefl _ (same ▸ excluded))
  obtain ⟨q, orthogonal, q_fixed, forward⟩ :=
    P.forward_tilt_direction x D (z - x) small_span different
  obtain ⟨t, _, tilted_support, larger⟩ :=
    P.tilt_contact_in_direction n x q support point orthogonal forward
  have equal_height : inner ℝ q z = inner ℝ q x := by
    have zero : inner ℝ q (z - x) = 0 := by rwa [real_inner_comm] at q_fixed
    simpa only [inner_sub_right, sub_eq_zero] using zero
  have still_excluded : inner ℝ (n + t • q) z < inner ℝ (n + t • q) x := by
    simp only [inner_add_left, inner_smul_left, conj_trivial, equal_height]
    linarith
  refine ⟨n + t • q, ?_, tilted_support, larger, still_excluded⟩
  intro zero
  simp only [zero, inner_zero_left, lt_self_iff_false] at still_excluded

end SixVertexUnfolding.ConvexPolyhedron
