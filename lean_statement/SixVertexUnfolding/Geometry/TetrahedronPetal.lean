import SixVertexUnfolding.Geometry.TriangleNondegeneracy
import SixVertexUnfolding.Geometry.TriangleStrictComparison
import SixVertexUnfolding.Geometry.OutwardTriangle

/-! Construct one outward tetrahedron petal, including its strict missing-vertex comparison. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Any tetrahedron side face can be unfolded outward from a fixed base placement. -/
theorem exists_tetrahedron_petal (P : ConvexPolyhedron) (size : P.vertices.card = 4)
    (source missing : P.Vertex) (distinct : missing ≠ source)
    (left : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ (P.oppositeFace size source).val,
      ∀ y ∈ (P.oppositeFace size source).val, dist (left x) (left y) = dist x y) :
    ∃ right : Space →ᵃ[ℝ] Plane,
      (∀ x ∈ (P.oppositeFace size missing).val,
        ∀ y ∈ (P.oppositeFace size missing).val, dist (right x) (right y) = dist x y) ∧
      (∀ x : P.Vertex, x ≠ source → x ≠ missing → right x = left x) ∧
      Disjoint (interior (left '' (P.oppositeFace size source).val))
        (interior (right '' (P.oppositeFace size missing).val)) ∧
      dist (missing : Space) source < dist (left missing) (right source) := by
  obtain ⟨a, b, ab, as_, am, bs, bm, remaining⟩ :=
    P.tetrahedron_remaining_pair size source missing distinct.symm
  let base := P.oppositeFace size source
  let petal := P.oppositeFace size missing
  have a_base : (a : Space) ∈ base.val := (P.vertex_mem_oppositeFace size source a).mpr as_
  have b_base : (b : Space) ∈ base.val := (P.vertex_mem_oppositeFace size source b).mpr bs
  have missing_base : (missing : Space) ∈ base.val :=
    (P.vertex_mem_oppositeFace size source missing).mpr distinct
  have a_petal : (a : Space) ∈ petal.val := (P.vertex_mem_oppositeFace size missing a).mpr am
  have b_petal : (b : Space) ∈ petal.val := (P.vertex_mem_oppositeFace size missing b).mpr bm
  have source_petal : (source : Space) ∈ petal.val :=
    (P.vertex_mem_oppositeFace size missing source).mpr distinct.symm
  have edge_length := left_rigid a a_base b b_base
  have placed_distinct : left a ≠ left b := by
    intro same
    have equal : (a : Space) = (b : Space) := dist_eq_zero.mp (by simpa [same] using edge_length.symm)
    exact ab (Subtype.ext equal)
  obtain ⟨right, right_rigid, at_a, at_b, outward⟩ := petal.exists_outward_placement
    a b missing source a_petal b_petal left edge_length placed_distinct
  have joined (x : P.Vertex) (xs : x ≠ source) (xm : x ≠ missing) : right x = left x := by
    rcases (remaining x).mp ⟨xs, xm⟩ with rfl | rfl
    exacts [at_a, at_b]
  have base_vertices : base.val ∩ (P.vertices : Set Space) =
      {(a : Space), (b : Space), (missing : Space)} := by
    ext x
    constructor
    · rintro ⟨in_base, vertex⟩
      let u : P.Vertex := ⟨x, vertex⟩
      have us : u ≠ source := (P.vertex_mem_oppositeFace size source u).mp in_base
      by_cases um : u = missing
      · exact Or.inr (Or.inr (congrArg Subtype.val um))
      · exact ((remaining u).mp ⟨us, um⟩).elim
          (fun equal => Or.inl (congrArg Subtype.val equal))
          (fun equal => Or.inr (Or.inl (congrArg Subtype.val equal)))
    · rintro (rfl | rfl | rfl)
      exacts [⟨a_base, a.property⟩, ⟨b_base, b.property⟩, ⟨missing_base, missing.property⟩]
  have petal_vertices : petal.val ∩ (P.vertices : Set Space) =
      {(a : Space), (b : Space), (source : Space)} := by
    ext x
    constructor
    · rintro ⟨in_petal, vertex⟩
      let u : P.Vertex := ⟨x, vertex⟩
      have um : u ≠ missing := (P.vertex_mem_oppositeFace size missing u).mp in_petal
      by_cases us : u = source
      · exact Or.inr (Or.inr (congrArg Subtype.val us))
      · exact ((remaining u).mp ⟨us, um⟩).elim
          (fun equal => Or.inl (congrArg Subtype.val equal))
          (fun equal => Or.inr (Or.inl (congrArg Subtype.val equal)))
    · rintro (rfl | rfl | rfl)
      exacts [⟨a_petal, a.property⟩, ⟨b_petal, b.property⟩, ⟨source_petal, source.property⟩]
  have base_shape : left '' base.val = convexHull ℝ {left a, left b, left missing} := by
    rw [base.eq_convexHull_vertices, base_vertices, left.image_convexHull]
    simp only [Set.image_insert_eq, Set.image_singleton]
  have petal_shape : right '' petal.val = convexHull ℝ {left a, left b, right source} := by
    rw [petal.eq_convexHull_vertices, petal_vertices, right.image_convexHull]
    simp only [Set.image_insert_eq, Set.image_singleton, at_a, at_b]
  have noncollinear := P.placed_triangle_noncollinear a b missing ab am bm
    (left a) (left b) (left missing) edge_length
    (left_rigid a a_base missing missing_base) (left_rigid b b_base missing missing_base)
  refine ⟨right, right_rigid, joined, ?_, ?_⟩
  · change Disjoint (interior (left '' base.val)) (interior (right '' petal.val))
    rw [base_shape, petal_shape]
    exact opposite_triangles_disjoint (left a) (left b) (left missing) (right source)
      noncollinear outward
  · apply two_triangles_distance_gt a b missing source
      (left a) (left b) (left missing) (right source)
      (fun equal => ab (Subtype.ext equal)) edge_length
      (left_rigid a a_base missing missing_base) (left_rigid b b_base missing missing_base)
      (by simpa only [at_a] using right_rigid a a_petal source source_petal)
      (by simpa only [at_b] using right_rigid b b_petal source source_petal) outward
    · exact P.no_three_collinear_vertices a.property b.property missing.property
        (fun equal => ab (Subtype.ext equal)) (fun equal => am (Subtype.ext equal))
        (fun equal => bm (Subtype.ext equal))
    · exact P.tetrahedron_vertex_outside_triangle_span size a b missing source as_ bs distinct

end SixVertexUnfolding.ConvexPolyhedron
