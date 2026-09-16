import SixVertexUnfolding.Geometry.EmbeddedCutGraph

/-! A finite straight graph has closed geometric component traces. These
lemmas translate connectedness of the actual trace into graph connectedness. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} (K : P.EmbeddedCutGraph a)

/-- A graph vertex on a closed edge is one of that edge's endpoints. -/
theorem vertex_on_edge {u v w : K.vertices} (edge : K.graph.Adj u v)
    (member : (w : Space) ∈ segment ℝ (u : Space) (v : Space)) : w = u ∨ w = v := by
  by_contra neither
  have wu : w ≠ u := fun equal => neither (Or.inl equal)
  have wv : w ≠ v := fun equal => neither (Or.inr equal)
  have inside := mem_openSegment_of_ne_left_right
    (fun equal => wu (Subtype.ext equal.symm)) (fun equal => wv (Subtype.ext equal.symm)) member
  exact disjoint_left.mp (K.no_vertex_inside u v edge) inside w.property

/-- If two closed edges meet, their first endpoints are in the same graph component. -/
theorem meeting_edges_reachable {u v w z : K.vertices}
    (first : K.graph.Adj u v) (second : K.graph.Adj w z) {x : Space}
    (hx : x ∈ segment ℝ (u : Space) (v : Space))
    (hy : x ∈ segment ℝ (w : Space) (z : Space)) : K.graph.Reachable u w := by
  by_cases vertex : x ∈ K.vertices
  · let q : K.vertices := ⟨x, vertex⟩
    have left := K.vertex_on_edge first (show (q : Space) ∈ segment ℝ (u : Space) (v : Space) from hx)
    have right := K.vertex_on_edge second (show (q : Space) ∈ segment ℝ (w : Space) (z : Space) from hy)
    have uq : K.graph.Reachable u q := by rcases left with rfl | rfl; exacts [.rfl, first.reachable]
    have wq : K.graph.Reachable w q := by rcases right with rfl | rfl; exacts [.rfl, second.reachable]
    exact uq.trans wq.symm
  · have interior {p q : K.vertices} (member : x ∈ segment ℝ (p : Space) (q : Space)) :
        x ∈ openSegment ℝ (p : Space) (q : Space) :=
      mem_openSegment_of_ne_left_right (fun equal => vertex (equal ▸ p.property))
        (fun equal => vertex (equal ▸ q.property)) member
    rcases K.open_edges_meet u v w z first second x (interior hx) (interior hy) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .rfl
    · exact second.symm.reachable

/-- Vertices in a chosen set together with edges whose first endpoint is in that set. -/
def subtrace (S : Set K.vertices) : Set Space :=
  Subtype.val '' S ∪ ⋃ u : K.vertices, ⋃ v : K.vertices,
    ⋃ (_ : u ∈ S ∧ K.graph.Adj u v), segment ℝ (u : Space) (v : Space)

theorem subtrace_closed (S : Set K.vertices) : IsClosed (K.subtrace S) := by
  letI : Finite K.vertices := K.finite_vertices
  apply ((Set.toFinite S).image Subtype.val).isClosed.union
  apply isClosed_iUnion_of_finite
  intro u
  apply isClosed_iUnion_of_finite
  intro v
  apply isClosed_iUnion_of_finite
  intro _
  let line : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap (u : Space) (v : Space)
  rw [segment_eq_image_lineMap]
  exact (isCompact_Icc.image line.continuous_of_finiteDimensional).isClosed

/-- A point in this trace is either a selected vertex or on an edge starting at one. -/
theorem mem_subtrace (S : Set K.vertices) (x : Space) : x ∈ K.subtrace S ↔
    (∃ u ∈ S, (u : Space) = x) ∨
    ∃ u ∈ S, ∃ v, K.graph.Adj u v ∧ x ∈ segment ℝ (u : Space) (v : Space) := by
  simp only [subtrace, mem_union, mem_image, mem_iUnion]
  aesop

/-- Intersection of two selected traces connects some selected vertex from each. -/
theorem subtrace_intersection {S T : Set K.vertices} {x : Space}
    (hx : x ∈ K.subtrace S) (hy : x ∈ K.subtrace T) :
    ∃ u ∈ S, ∃ v ∈ T, K.graph.Reachable u v := by
  rw [K.mem_subtrace] at hx hy
  rcases hx with ⟨u, hu, rfl⟩ | ⟨u, hu, v, first, hx⟩
  · rcases hy with ⟨v, hv, same⟩ | ⟨v, hv, w, edge, member⟩
    · exact ⟨u, hu, v, hv, (Subtype.ext same : v = u) ▸ SimpleGraph.Reachable.rfl⟩
    · refine ⟨u, hu, v, hv, ?_⟩
      rcases K.vertex_on_edge edge member with rfl | rfl
      · exact .rfl
      · exact edge.symm.reachable
  · rcases hy with ⟨w, hw, rfl⟩ | ⟨w, hw, z, second, hy⟩
    · refine ⟨u, hu, w, hw, ?_⟩
      rcases K.vertex_on_edge first hx with rfl | rfl
      · exact .rfl
      · exact first.reachable
    · exact ⟨u, hu, w, hw, K.meeting_edges_reachable first second hx hy⟩

end SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph
