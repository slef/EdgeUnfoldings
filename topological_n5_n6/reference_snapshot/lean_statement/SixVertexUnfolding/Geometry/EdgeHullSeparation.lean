import SixVertexUnfolding.Geometry.EdgeIntersections

/-! An original edge is separated from the convex hull of all its other original vertices. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- A genuine vertex is outside the convex hull of any original vertices excluding it. -/
theorem vertex_not_mem_hull_others (P : ConvexPolyhedron) (v : P.Vertex) :
    (v : Space) ∉ convexHull ℝ ((P.vertices : Set Space) \ {(v : Space)}) := by
  have extreme : (v : Space) ∈ P.body.extremePoints ℝ := by
    rw [P.body_extreme_points]
    exact v.property
  have excluded := (P.body_convex.mem_extremePoints_iff_mem_diff_convexHull_diff.mp extreme).2
  intro member
  apply excluded
  apply convexHull_mono (show (P.vertices : Set Space) \ {(v : Space)} ⊆ P.body \ {(v : Space)} from ?_) member
  exact fun _ hx => ⟨P.vertices_subset_body hx.1, hx.2⟩

/-- The whole segment of an original edge misses the hull of every other original vertex. -/
theorem edge_disjoint_hull_others (P : ConvexPolyhedron) (a b : P.Vertex)
    (edge : P.edgeGraph.Adj a b) :
    Disjoint (segment ℝ (a : Space) (b : Space))
      (convexHull ℝ ((P.vertices : Set Space) \ {(a : Space), (b : Space)})) := by
  obtain ⟨height, exposed⟩ := P.edgeGraph_segment_isExposed edge
    (show (segment ℝ (a : Space) (b : Space)).Nonempty from
      ⟨a, left_mem_segment ℝ (a : Space) (b : Space)⟩)
  have a_max := (exposed ▸ (left_mem_segment ℝ (a : Space) (b : Space))).2
  have below : ∀ x ∈ (P.vertices : Set Space) \ {(a : Space), (b : Space)}, height x < height a := by
    rintro x ⟨vertex, other⟩
    apply lt_of_le_of_ne (a_max x (P.vertices_subset_body vertex))
    intro same
    have on_edge : x ∈ segment ℝ (a : Space) (b : Space) := by
      rw [exposed]
      exact ⟨P.vertices_subset_body vertex, fun y hy => same ▸ a_max y hy⟩
    rcases P.vertex_in_segment_is_endpoint vertex (P.vertices_subset_body a.property)
      (P.vertices_subset_body b.property) on_edge with at_a | at_b
    · exact other (Or.inl at_a.symm)
    · exact other (Or.inr at_b.symm)
  have hull_below : ∀ x ∈ convexHull ℝ ((P.vertices : Set Space) \ {(a : Space), (b : Space)}),
      height x < height a :=
    convexHull_min below (convex_halfSpace_lt
      ⟨height.map_add, height.map_smul⟩ (height a))
  apply Set.disjoint_left.mpr
  intro x on_edge in_hull
  have x_max := (exposed ▸ on_edge).2
  exact (not_lt_of_ge (x_max a (P.vertices_subset_body a.property))) (hull_below x in_hull)

end SixVertexUnfolding.ConvexPolyhedron
