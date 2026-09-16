import SixVertexUnfolding.Geometry.SupportingContacts

/-! Elementary bounds on the number of original vertices in each facet. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- A two-dimensional facet contains at least three original vertices. -/
theorem three_le_vertex_count : 3 ≤ (F.val ∩ (P.vertices : Set Space)).ncard := by
  classical
  let vertices := F.val ∩ (P.vertices : Set Space)
  have finite_vertices : vertices.Finite := P.vertices.finite_toSet.subset Set.inter_subset_right
  letI : Fintype vertices := finite_vertices.fintype
  have hull_nonempty := F.nonempty
  rw [F.eq_convexHull_vertices] at hull_nonempty
  haveI : Nonempty vertices := (convexHull_nonempty_iff.mp hull_nonempty).to_subtype
  have dimension_bound := finrank_vectorSpan_range_add_one_le ℝ
    (fun x : vertices => (x : Space))
  rw [Subtype.range_coe] at dimension_bound
  have dimension := F.property.1
  rw [F.eq_convexHull_vertices, affineDimension_convexHull] at dimension
  change Module.finrank ℝ (affineSpan ℝ vertices).direction = 2 at dimension
  rw [direction_affineSpan] at dimension
  rw [dimension] at dimension_bound
  simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using dimension_bound

/-- A facet cannot contain every original vertex of a three-dimensional solid. -/
theorem exists_vertex_outside : ∃ v ∈ P.vertices, v ∉ F.val := by
  obtain ⟨_, n, level, nonzero, _, face_eq⟩ := F.property
  obtain ⟨x, hx⟩ := F.nonempty
  have x_height := (face_eq ▸ hx).2
  obtain ⟨v, hv, different⟩ := P.exists_vertex_height_ne n x nonzero
  refine ⟨v, hv, ?_⟩
  intro in_face
  exact different (((face_eq ▸ in_face).2).trans x_height.symm)

/-- A facet uses strictly fewer vertices than the whole solid. -/
theorem vertex_count_lt : (F.val ∩ (P.vertices : Set Space)).ncard < P.vertices.card := by
  obtain ⟨v, hv, outside⟩ := F.exists_vertex_outside
  have proper : F.val ∩ (P.vertices : Set Space) ⊂ (P.vertices : Set Space) := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_right, ?_⟩
    intro equal
    have member : v ∈ F.val ∩ (P.vertices : Set Space) := equal.symm ▸ hv
    exact outside member.1
  simpa using Set.ncard_lt_ncard proper P.vertices.finite_toSet

end SixVertexUnfolding.ConvexPolyhedron.Face
