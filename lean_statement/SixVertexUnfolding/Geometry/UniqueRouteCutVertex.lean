import SixVertexUnfolding.Geometry.RouteBoundarySides
import SixVertexUnfolding.Geometry.StripEndpointBoundary
import SixVertexUnfolding.Geometry.CutEdgeTriangles
import SixVertexUnfolding.Geometry.SourceNeighborhood

/-! A tree vertex reached by a unique shortest route has at most one
incident edge. Two edges would put at least three disjoint open strips
along the same route, contrary to its two local sides. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- A unique route to a cut-tree vertex rules out two different neighbors. -/
theorem unique_route_cut_vertex_at_most_one_neighbor (a : frontier P.body) (T : P.CutLocusTree a)
    (u : T.vertices) (unique : (P.geodesicFiber a (T.vertexTarget u)).Subsingleton)
    (v w : T.vertices) (edge : T.graph.Adj u v) (other : T.graph.Adj u w) : v = w := by
  classical
  by_contra different_neighbors
  obtain ⟨D⟩ := graph.exists_cut_edge_triangles small_faces a T edge
  obtain ⟨E⟩ := graph.exists_cut_edge_triangles small_faces a T other
  let f := D.first 0
  have member : f ∈ P.geodesicFiber a (T.vertexTarget u) := by
    simpa only [T.closedEdgeTarget_zero] using (D.member 0).1
  have same_second : D.second 0 = f := unique
    (by simpa only [T.closedEdgeTarget_zero] using (D.member 0).2) member
  have same_other : E.first 0 = f := unique
    (by simpa only [T.closedEdgeTarget_zero] using (E.member 0).1) member
  have different : a ≠ T.vertexTarget u := by
    intro same
    have cut := T.vertexTarget_cut u
    rw [← same] at cut
    exact P.source_not_cutSet a cut
  let m : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have after_start : 0 < m := by change (0 : ℝ) < 1 / 2; norm_num
  have before_end : m < 1 := by change (1 / 2 : ℝ) < 1; norm_num
  have nonvertex : (f m : Space) ∉ P.vertices := by
    obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f member.1
    apply graph.simple_shortest_avoids_vertices small_faces (P.surfacePathOfCurve f)
      shortest finite ?_ m after_start before_end
    intro s t same
    exact P.geodesicFiber_injective a (T.vertexTarget u) different f member (Subtype.ext same)
  have opensD := graph.cut_edge_strips_open small_faces a T edge D.strips
  have opensE := graph.cut_edge_strips_open small_faces a T other E.strips
  obtain ⟨limit₀, U₀, open₀, center₀, boundary₀⟩ :=
    graph.strip_frontier_near_endpoint_route small_faces a T edge D.strips.first D.first
      (fun t => (D.agrees t).1) (fun t => (D.member t).1) opensD.1 m after_start before_end
  obtain ⟨limit₁, U₁, open₁, center₁, boundary₁⟩ :=
    graph.strip_frontier_near_endpoint_route small_faces a T edge D.strips.second D.second
      (fun t => (D.agrees t).2) (fun t => (D.member t).2) opensD.2 m after_start before_end
  obtain ⟨limit₂, U₂, open₂, center₂, boundary₂⟩ :=
    graph.strip_frontier_near_endpoint_route small_faces a T other E.strips.first E.first
      (fun t => (E.agrees t).1) (fun t => (E.member t).1) opensE.1 m after_start before_end
  rw [same_second] at limit₁ center₁ boundary₁
  rw [same_other] at limit₂ center₂ boundary₂
  let regions : Fin 3 → Set (frontier P.body) :=
    ![routeStrip D.strips.first, routeStrip D.strips.second, routeStrip E.strips.first]
  have open_regions : ∀ i, IsOpen (regions i) := by
    intro i
    fin_cases i
    · exact opensD.1
    · exact opensD.2
    · exact opensE.1
  have disjoint₀₁ := graph.cut_edge_strips_disjoint small_faces a T edge D.strips
  have edges_different : ¬ ((u = u ∧ v = w) ∨ (u = w ∧ v = u)) := by
    rintro (⟨_, same⟩ | ⟨_, same⟩)
    · exact different_neighbors same
    · exact edge.ne same.symm
  have pairs := graph.distinct_cut_edge_strips_disjoint small_faces a T edge other
    edges_different D.strips E.strips
  have disjoint₀₂ : Disjoint (routeStrip D.strips.first) (routeStrip E.strips.first) :=
    pairs.mono subset_union_left subset_union_left
  have disjoint₁₂ : Disjoint (routeStrip D.strips.second) (routeStrip E.strips.first) :=
    pairs.mono subset_union_right subset_union_left
  have separate : Pairwise (fun i j => Disjoint (regions i) (regions j)) := by
    intro i j different
    fin_cases i <;> fin_cases j <;> try exact (different rfl).elim
    · exact disjoint₀₁
    · exact disjoint₀₂
    · exact disjoint₀₁.symm
    · exact disjoint₁₂
    · exact disjoint₀₂.symm
    · exact disjoint₁₂.symm
  apply P.not_three_regions_along_route a (T.vertexTarget u) different f member m
    after_start before_end nonvertex regions open_regions separate
    (fun i => ?_) (U₀ ∩ U₁ ∩ U₂) ((open₀.inter open₁).inter open₂)
    ⟨⟨center₀, center₁⟩, center₂⟩ (fun i => ?_)
  · fin_cases i
    · exact limit₀
    · exact limit₁
    · exact limit₂
  · rintro x ⟨boundary, near⟩
    fin_cases i
    · exact boundary₀ ⟨boundary, near.1.1⟩
    · exact boundary₁ ⟨boundary, near.1.2⟩
    · exact boundary₂ ⟨boundary, near.2⟩

include graph small_faces in
/-- Cofacial source and target already supply the required uniqueness. -/
theorem cofacial_cut_vertex_at_most_one_neighbor (a : frontier P.body) (T : P.CutLocusTree a)
    (u : T.vertices) (F : P.Face) (source : (a : Space) ∈ F.val) (target : (u : Space) ∈ F.val)
    (v w : T.vertices) (edge : T.graph.Adj u v) (other : T.graph.Adj u w) : v = w :=
  graph.unique_route_cut_vertex_at_most_one_neighbor small_faces a T u
    (P.geodesicFiber_cofacial_unique a (T.vertexTarget u) F source target) v w edge other

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
