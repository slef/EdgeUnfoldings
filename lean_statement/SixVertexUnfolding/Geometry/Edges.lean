import SixVertexUnfolding.Geometry.Intersections

/-!
The public `ShareEdge` predicate means a complete segment with two original vertices.
No triangulation or additional vertices are introduced.
-/

namespace SixVertexUnfolding.ConvexPolyhedron

variable (P : ConvexPolyhedron)

/-- An original vertex cannot lie strictly between two points of the solid. -/
theorem vertex_in_segment_is_endpoint {a b v : Space}
    (vertex : v ∈ P.vertices) (a_in : a ∈ P.body) (b_in : b ∈ P.body)
    (between : v ∈ segment ℝ a b) : a = v ∨ b = v := by
  have extreme : v ∈ P.body.extremePoints ℝ := by
    rw [P.body_extreme_points]
    exact vertex
  exact (mem_extremePoints_iff_forall_segment.mp extreme).2 a a_in b b_in between

/-- Three distinct original vertices cannot be collinear. -/
theorem no_three_collinear_vertices {a b c : Space}
    (ha : a ∈ P.vertices) (hb : b ∈ P.vertices) (hc : c ∈ P.vertices)
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    ¬ Collinear ℝ ({a, b, c} : Set Space) := by
  intro collinear
  have a_in := P.vertices_subset_body ha
  have b_in := P.vertices_subset_body hb
  have c_in := P.vertices_subset_body hc
  rcases collinear.wbtw_or_wbtw_or_wbtw with middle_b | middle_c | middle_a
  · have endpoint := P.vertex_in_segment_is_endpoint hb a_in c_in middle_b.mem_segment
    rcases endpoint with equal | equal
    · exact ab equal
    · exact bc equal.symm
  · have endpoint := P.vertex_in_segment_is_endpoint hc b_in a_in middle_c.mem_segment
    rcases endpoint with equal | equal
    · exact bc equal
    · exact ac equal
  · have endpoint := P.vertex_in_segment_is_endpoint ha c_in b_in middle_a.mem_segment
    rcases endpoint with equal | equal
    · exact ac equal.symm
    · exact ab equal.symm

namespace Face

variable {P} (F G : P.Face)

theorem shareEdge_irrefl : ¬ P.ShareEdge F F := by
  change affineDimension (F.val ∩ F.val) ≠ 1
  rw [Set.inter_self, F.property.1]
  norm_num

theorem shareEdge_symm (shared : P.ShareEdge F G) : P.ShareEdge G F := by
  simpa only [ShareEdge, Set.inter_comm] using shared

/-- Every shared edge has exactly two original vertices. -/
theorem shared_vertices_eq_pair (shared : P.ShareEdge F G) :
    ∃ a b : Space, a ≠ b ∧
      (F.val ∩ G.val) ∩ (P.vertices : Set Space) = {a, b} := by
  let common := (F.val ∩ G.val) ∩ (P.vertices : Set Space)
  have hull_eq : F.val ∩ G.val = convexHull ℝ common :=
    F.intersection_eq_convexHull_vertices G
  have common_dimension : affineDimension common = 1 := by
    rw [← affineDimension_convexHull, ← hull_eq]
    exact shared
  have common_nonempty := nonempty_of_affineDimension_pos (s := common) (by omega)
  obtain ⟨a, ha⟩ := common_nonempty
  have second : ∃ b ∈ common, b ≠ a := by
    by_contra no_second
    push Not at no_second
    have inclusion : common ⊆ {a} := fun x hx => no_second x hx
    have dimension_bound := affineDimension_mono inclusion
    rw [common_dimension, affineDimension_singleton] at dimension_bound
    omega
  obtain ⟨b, hb, ba⟩ := second
  refine ⟨a, b, ba.symm, ?_⟩
  have distinct : F ≠ G := by
    intro equal
    subst G
    exact F.shareEdge_irrefl shared
  have collinear : Collinear ℝ (F.val ∩ G.val) := by
    apply collinear_iff_finrank_le_one.mpr
    have bound := F.intersection_dimension_le_one G distinct
    change Module.finrank ℝ (affineSpan ℝ (F.val ∩ G.val)).direction ≤ 1 at bound
    rw [direction_affineSpan] at bound
    exact bound
  apply Set.Subset.antisymm
  · intro x hx
    by_cases xa : x = a
    · simp [xa]
    by_cases xb : x = b
    · simp [xb]
    exfalso
    have triple_collinear : Collinear ℝ ({a, b, x} : Set Space) :=
      collinear.subset (by
        intro y hy
        rcases hy with rfl | rfl | rfl
        exacts [ha.1, hb.1, hx.1])
    exact P.no_three_collinear_vertices ha.2 hb.2 hx.2 ba.symm (Ne.symm xa) (Ne.symm xb)
      triple_collinear
  · intro x hx
    rcases hx with rfl | rfl
    exacts [ha, hb]

/-- A shared edge is precisely the full segment joining its two original endpoints. -/
theorem shared_edge_endpoints (shared : P.ShareEdge F G) :
    ∃ a ∈ P.vertices, ∃ b ∈ P.vertices, a ≠ b ∧ F.val ∩ G.val = segment ℝ a b := by
  obtain ⟨a, b, distinct, common_eq⟩ := F.shared_vertices_eq_pair G shared
  have a_common : a ∈ (F.val ∩ G.val) ∩ (P.vertices : Set Space) := by
    rw [common_eq]
    simp
  have b_common : b ∈ (F.val ∩ G.val) ∩ (P.vertices : Set Space) := by
    rw [common_eq]
    simp
  refine ⟨a, a_common.2, b, b_common.2, distinct, ?_⟩
  rw [F.intersection_eq_convexHull_vertices G, common_eq, convexHull_pair]

end Face

/-- The geometric dual graph: vertices are whole facets, adjacency means a shared original edge. -/
def dualGraph : SimpleGraph P.Face where
  Adj := P.ShareEdge
  symm := fun F G => F.shareEdge_symm G
  loopless := ⟨fun F => F.shareEdge_irrefl⟩

end SixVertexUnfolding.ConvexPolyhedron

namespace SixVertexUnfolding.EdgeUnfolding

variable {P : ConvexPolyhedron} (net : EdgeUnfolding P)

/-- The retained hinge tree is a spanning subgraph of the geometric dual graph. -/
theorem hinges_le_dualGraph : net.hinges ≤ P.dualGraph := by
  intro F G adjacent
  exact net.original_edges F G adjacent

end SixVertexUnfolding.EdgeUnfolding
