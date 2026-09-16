import SixVertexUnfolding.Geometry.VertexFigureEdges

/-!
A nonmaximal vertex has an ascending original edge for every linear height.
Maximizing height in a graph component then proves connectivity.
-/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- If some original vertex is higher, an original edge already leads to a higher vertex. -/
theorem exists_ascending_neighbor (P : ConvexPolyhedron) (height : Space) (v : P.Vertex)
    (not_maximal : ∃ w : P.Vertex, inner ℝ height v < inner ℝ height w) :
    ∃ w : P.Vertex, P.edgeGraph.Adj v w ∧ inner ℝ height v < inner ℝ height w := by
  obtain ⟨normal, strict⟩ := P.vertex_strict_support v.property
  let figure : VertexFigure P v := ⟨normal, strict⟩
  obtain ⟨higher, increase⟩ := not_maximal
  have distinct : (higher : Space) ≠ (v : Space) := by
    intro equal
    exact increase.ne (congrArg (inner ℝ height) equal).symm
  have positive_ray : 0 < inner ℝ height (figure.direction higher) := by
    have positive_product : 0 < figure.gap higher * inner ℝ height (figure.direction higher) := by
      rw [← figure.vertex_height_difference height higher.property distinct]
      exact sub_pos.mpr increase
    exact pos_of_mul_pos_right positive_product (figure.gap_pos higher.property distinct).le
  have ascending_corner : ∃ p ∈ figure.corners, 0 < inner ℝ height p := by
    by_contra none
    push Not at none
    have hull_bound : convexHull ℝ figure.corners ⊆ {p | inner ℝ height p ≤ 0} :=
      convexHull_min none (convex_halfSpace_le
        ⟨fun a b => inner_add_right height a b, fun a b => inner_smul_right height b a⟩ 0)
    have in_hull : figure.direction higher ∈ convexHull ℝ figure.corners := by
      rw [figure.corners_hull]
      exact subset_convexHull ℝ _ ⟨higher, ⟨higher.property, distinct⟩, rfl⟩
    exact (not_le_of_gt positive_ray) (hull_bound in_hull)
  obtain ⟨p, corner, positive⟩ := ascending_corner
  obtain ⟨w, adjacent, direction_eq⟩ := figure.corner_is_neighbor corner
  refine ⟨w, adjacent, ?_⟩
  have different : (w : Space) ≠ (v : Space) :=
    fun equal => adjacent.ne (Subtype.ext equal.symm)
  apply sub_pos.mp
  rw [figure.vertex_height_difference height w.property different, direction_eq]
  exact mul_pos (figure.gap_pos w.property different) positive

/-- The original vertex-edge graph of every solid convex polyhedron is connected. -/
theorem edgeGraph_connected (P : ConvexPolyhedron) : P.edgeGraph.Connected := by
  classical
  letI : Nonempty P.Vertex := P.vertices_nonempty.to_subtype
  refine ⟨?_⟩
  intro start target
  obtain ⟨height, strict⟩ := P.vertex_strict_support target.property
  let component := Finset.univ.filter (fun w : P.Vertex => P.edgeGraph.Reachable start w)
  have start_in : start ∈ component := by
    simp only [component, Finset.mem_filter, Finset.mem_univ, true_and]
    exact SimpleGraph.Reachable.rfl
  obtain ⟨highest, highest_in, maximal⟩ := component.exists_max_image
    (fun w : P.Vertex => inner ℝ height w) ⟨start, start_in⟩
  have reached : P.edgeGraph.Reachable start highest := (Finset.mem_filter.mp highest_in).2
  by_cases same : highest = target
  · exact same ▸ reached
  have lower := strict highest highest.property
    (show (highest : Space) ≠ (target : Space) from fun equal => same (Subtype.ext equal))
  obtain ⟨next, adjacent, higher⟩ := P.exists_ascending_neighbor height highest ⟨target, lower⟩
  have next_in : next ∈ component :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, reached.trans adjacent.reachable⟩
  exact False.elim (higher.not_ge (maximal next next_in))

end SixVertexUnfolding.ConvexPolyhedron
