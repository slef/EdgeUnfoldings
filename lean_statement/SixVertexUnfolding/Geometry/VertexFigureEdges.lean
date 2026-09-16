import SixVertexUnfolding.Geometry.VertexFigure

/-! Corners of a vertex figure give distinct original edge neighbors. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFigure

variable {P : ConvexPolyhedron} {v : P.Vertex} (figure : VertexFigure P v)

/-- An exposing height on the figure becomes a supporting plane through the original vertex. -/
theorem corner_support_normal {p : Space} (corner : p ∈ figure.corners) :
    ∃ m : Space, (∀ q ∈ figure.points, inner ℝ m q ≤ 0) ∧
      (∀ q ∈ figure.points, inner ℝ m q = 0 ↔ q = p) := by
  obtain ⟨height, strict⟩ := finite_extreme_strict_support figure.points figure.points_finite corner
  let m := height + inner ℝ height p • figure.normal
  have value (q : Space) (hq : q ∈ figure.points) :
      inner ℝ m q = inner ℝ height q - inner ℝ height p := by
    simp [m, inner_add_left, inner_smul_left, figure.points_height hq, sub_eq_add_neg]
  refine ⟨m, ?_, ?_⟩
  · intro q hq
    rw [value q hq]
    by_cases same : q = p
    · simp [same]
    · exact sub_nonpos.mpr (strict q hq same).le
  · intro q hq
    rw [value q hq, sub_eq_zero]
    constructor
    · intro equal
      by_contra distinct
      exact (strict q hq distinct).ne equal
    · rintro rfl
      rfl

theorem vertex_height_difference (m : Space) {w : Space} (vertex : w ∈ P.vertices)
    (distinct : w ≠ (v : Space)) :
    inner ℝ m w - inner ℝ m v = figure.gap w * inner ℝ m (figure.direction w) := by
  rw [← inner_sub_right, ← figure.reconstruct vertex distinct, inner_smul_right]

/-- Each corner is the ray to an original edge neighbor, with no extra vertices introduced. -/
theorem corner_is_neighbor {p : Space} (corner : p ∈ figure.corners) :
    ∃ w : P.Vertex, P.edgeGraph.Adj v w ∧ figure.direction w = p := by
  classical
  obtain ⟨w, ⟨vertex, distinct⟩, direction_eq⟩ := figure.corners_subset_points corner
  let b : P.Vertex := ⟨w, vertex⟩
  have distinct_vertices : v ≠ b := by
    intro equal
    exact distinct (congrArg Subtype.val equal).symm
  obtain ⟨m, bounds, zeros⟩ := figure.corner_support_normal corner
  have support : P.SupportsAt m v := by
    apply P.supportsAt_of_vertex_bounds
    intro u hu
    by_cases same : u = (v : Space)
    · simp [same]
    · have below := mul_nonpos_of_nonneg_of_nonpos (figure.gap_pos hu same).le
        (bounds _ ⟨u, ⟨hu, same⟩, rfl⟩)
      rw [← figure.vertex_height_difference m hu same] at below
      exact sub_nonpos.mp below
  have active (u : Space) (hu : u ∈ P.vertices) :
      inner ℝ m u = inner ℝ m v ↔ u = (v : Space) ∨ u = w := by
    by_cases same : u = (v : Space)
    · simp [same]
    have positive := figure.gap_pos hu same
    have difference := figure.vertex_height_difference m hu same
    have ray_zero := zeros _ (show figure.direction u ∈ figure.points from ⟨u, ⟨hu, same⟩, rfl⟩)
    constructor
    · intro equal
      have zero : inner ℝ m (figure.direction u) = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left positive.ne'
        rw [← difference, equal, sub_self]
      have same_ray : figure.direction u = figure.direction w :=
        (ray_zero.mp zero).trans direction_eq.symm
      exact Or.inr (figure.direction_injective ⟨hu, same⟩ ⟨vertex, distinct⟩ same_ray)
    · rintro (equal | equal)
      · exact False.elim (same equal)
      · have zero := ray_zero.mpr (equal ▸ direction_eq)
        rw [zero, mul_zero] at difference
        exact sub_eq_zero.mp difference
  have contacts : (P.contactVertices m v : Set Space) = {(v : Space), (b : Space)} := by
    ext u
    simp only [contactVertices, Finset.mem_coe, Finset.mem_filter,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hu, equal⟩
      exact (active u hu).mp equal
    · intro member
      have hu : u ∈ P.vertices := by
        rcases member with rfl | rfl
        exacts [v.property, b.property]
      exact ⟨hu, (active u hu).mpr member⟩
  exact ⟨b, P.edgeGraph_adj_of_contact_pair v b distinct_vertices m
    (P.normal_ne_zero_of_contact_pair v b distinct_vertices m contacts) support contacts,
    direction_eq⟩

/-- Distinct figure corners supply distinct edge neighbors. -/
theorem corner_count_le_degree : Nat.card figure.corners ≤ P.edgeGraph.degree v := by
  classical
  have neighbors (p : figure.corners) := figure.corner_is_neighbor p.property
  choose neighbor adjacent direction_eq using neighbors
  let into_neighbors : figure.corners → P.edgeGraph.neighborSet v :=
    fun p => ⟨neighbor p, adjacent p⟩
  have injective : Function.Injective into_neighbors := by
    intro p q same
    have same_vertex : neighbor p = neighbor q := congrArg Subtype.val same
    apply Subtype.ext
    exact (direction_eq p).symm.trans ((congrArg (fun w : P.Vertex => figure.direction w)
      same_vertex).trans (direction_eq q))
  have bound := Nat.card_le_card_of_injective into_neighbors injective
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] using bound

end SixVertexUnfolding.ConvexPolyhedron.VertexFigure

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Every original vertex of a solid convex polyhedron has at least three original edge neighbors. -/
theorem edgeGraph_min_degree (P : ConvexPolyhedron) (v : P.Vertex) :
    3 ≤ P.edgeGraph.degree v := by
  obtain ⟨normal, strict⟩ := P.vertex_strict_support v.property
  let figure : VertexFigure P v := ⟨normal, strict⟩
  exact figure.three_le_corner_count.trans figure.corner_count_le_degree

end SixVertexUnfolding.ConvexPolyhedron
