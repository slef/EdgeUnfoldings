import SixVertexUnfolding.Definitions

/-! Basic consequences of the public definition of a convex polyhedron. -/

namespace SixVertexUnfolding.ConvexPolyhedron

variable (P : ConvexPolyhedron)

theorem body_convex : Convex ℝ P.body :=
  convex_convexHull ℝ _

theorem body_compact : IsCompact P.body :=
  P.vertices.finite_toSet.isCompact_convexHull ℝ

theorem body_closed : IsClosed P.body :=
  P.body_compact.isClosed

theorem body_nonempty : P.body.Nonempty :=
  P.solid.mono interior_subset

theorem vertices_subset_body : (P.vertices : Set Space) ⊆ P.body :=
  subset_convexHull ℝ _

theorem vertices_nonempty : P.vertices.Nonempty := by
  exact convexHull_nonempty_iff.mp P.body_nonempty

theorem vertices_span_space : affineSpan ℝ (P.vertices : Set Space) = ⊤ :=
  affineSpan_eq_top_of_nonempty_interior P.solid

theorem body_extreme_points : P.body.extremePoints ℝ = (P.vertices : Set Space) :=
  P.vertices_exact.symm

/-- A solid in three-space requires at least four vertices. -/
theorem four_le_vertex_count : 4 ≤ P.vertices.card := by
  classical
  haveI : Nonempty (P.vertices : Set Space) := P.vertices_nonempty.to_subtype
  have dimension_bound := finrank_vectorSpan_range_add_one_le ℝ
    (fun x : (P.vertices : Set Space) => (x : Space))
  have span_eq : vectorSpan ℝ (P.vertices : Set Space) = ⊤ :=
    AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ Space Space
      P.vertices_span_space
  have range_eq : Set.range (fun x : (P.vertices : Set Space) => (x : Space)) =
      (P.vertices : Set Space) := Subtype.range_coe
  rw [range_eq, span_eq] at dimension_bound
  simpa [finrank_top, Space] using dimension_bound

/-- These are exactly the vertex counts needed by the main theorem. -/
theorem vertex_count_cases (at_most_six : P.vertices.card ≤ 6) :
    P.vertices.card = 4 ∨ P.vertices.card = 5 ∨ P.vertices.card = 6 := by
  have at_least_four := P.four_le_vertex_count
  omega

end SixVertexUnfolding.ConvexPolyhedron
