import SixVertexUnfolding.Geometry.EdgeFacePairs

/-! Distinct original facets can share two original vertices only along an original edge. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F G : P.Face)

/-- Two common, distinct original vertices certify an original edge between distinct facets. -/
theorem adjacent_of_common_vertices (different : F ≠ G) (a b : P.Vertex) (ab : a ≠ b)
    (aF : (a : Space) ∈ F.val) (bF : (b : Space) ∈ F.val)
    (aG : (a : Space) ∈ G.val) (bG : (b : Space) ∈ G.val) : P.edgeGraph.Adj a b := by
  have distinct_points : (a : Space) ≠ (b : Space) := fun same => ab (Subtype.ext same)
  have pair_subset : ({(a : Space), (b : Space)} : Set Space) ⊆ F.val ∩ G.val := by
    rintro x (rfl | rfl)
    exacts [⟨aF, aG⟩, ⟨bF, bG⟩]
  have lower := affineDimension_mono pair_subset
  rw [affineDimension_pair distinct_points] at lower
  have upper := F.intersection_dimension_le_one G different
  have shared : P.ShareEdge F G := Nat.le_antisymm upper lower
  obtain ⟨x, y, xy, common⟩ := F.shared_vertices_eq_pair G shared
  have at_a : (a : Space) = x ∨ (a : Space) = y := by
    have member : (a : Space) ∈ (F.val ∩ G.val) ∩ (P.vertices : Set Space) := ⟨⟨aF, aG⟩, a.property⟩
    simpa only [common, Set.mem_insert_iff, Set.mem_singleton_iff] using member
  have at_b : (b : Space) = x ∨ (b : Space) = y := by
    have member : (b : Space) ∈ (F.val ∩ G.val) ∩ (P.vertices : Set Space) := ⟨⟨bF, bG⟩, b.property⟩
    simpa only [common, Set.mem_insert_iff, Set.mem_singleton_iff] using member
  refine ⟨ab, F, G, shared, ?_⟩
  rw [F.intersection_eq_convexHull_vertices G, common, convexHull_pair]
  rcases at_a with ax | ay <;> rcases at_b with bx | byy
  · exact (distinct_points (ax.trans bx.symm)).elim
  · rw [ax, byy]
  · rw [ay, bx, segment_symm]
  · exact (distinct_points (ay.trans byy.symm)).elim

/-- A nonedge pair belongs to at most one original facet. -/
theorem eq_of_common_nonedge (a b : P.Vertex) (ab : a ≠ b) (nonedge : ¬ P.edgeGraph.Adj a b)
    (aF : (a : Space) ∈ F.val) (bF : (b : Space) ∈ F.val)
    (aG : (a : Space) ∈ G.val) (bG : (b : Space) ∈ G.val) : F = G := by
  by_contra different
  exact nonedge (F.adjacent_of_common_vertices G different a b ab aF bF aG bG)

end SixVertexUnfolding.ConvexPolyhedron.Face
