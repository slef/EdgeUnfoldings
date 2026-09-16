import SixVertexUnfolding.Geometry.StraightShortestPaths
import SixVertexUnfolding.Geometry.EdgeIntersections

/-! The universal-vertex case supplies five noncrossing shortest original-edge cuts.
The nonoverlap theorem for the surface developed after these cuts remains separate. -/

namespace SixVertexUnfolding

/-- The five edges from one of six vertices to all the others. -/
def sixVertexStar (source : Fin 6) : SimpleGraph (Fin 6) where
  Adj a b := a ≠ b ∧ (a = source ∨ b = source)
  symm := fun _ _ edge => ⟨edge.1.symm, edge.2.symm⟩
  loopless := ⟨fun _ edge => edge.1 rfl⟩

instance (source : Fin 6) : DecidableRel (sixVertexStar source).Adj := by
  unfold sixVertexStar
  infer_instance

theorem sixVertexStar_isTree (source : Fin 6) : (sixVertexStar source).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨source, ?_⟩
    intro v
    by_cases same : source = v
    · subst v
      exact SimpleGraph.Reachable.rfl
    · exact (show (sixVertexStar source).Adj source v from ⟨same, Or.inl rfl⟩).reachable
  · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
    fin_cases source <;> decide

namespace ConvexPolyhedron

/-- Cutting all five edges at a universal vertex cuts an actual spanning tree of original edges. -/
theorem six_vertex_source_cut_tree (P : ConvexPolyhedron) (size : P.vertices.card = 6)
    (source : P.Vertex) (universal : ∀ v, v ≠ source → P.edgeGraph.Adj source v) :
    ∃ cuts : SimpleGraph P.Vertex, cuts.IsTree ∧
      ∀ a b, cuts.Adj a b ↔ P.edgeGraph.Adj a b ∧ (a = source ∨ b = source) := by
  let index : Fin 6 ≃ P.Vertex := (Fintype.equivFinOfCardEq (by simpa [Vertex] using size)).symm
  let cuts := (sixVertexStar (index.symm source)).comap index.symm
  have tree : cuts.IsTree :=
    (SimpleGraph.Iso.comap index.symm (sixVertexStar (index.symm source))).isTree_iff.mpr
      (sixVertexStar_isTree _)
  refine ⟨cuts, tree, ?_⟩
  intro a b
  change (index.symm a ≠ index.symm b ∧
    (index.symm a = index.symm source ∨ index.symm b = index.symm source)) ↔ _
  simp only [ne_eq, index.symm.injective.eq_iff]
  constructor
  · rintro ⟨different, at_source⟩
    refine ⟨?_, at_source⟩
    rcases at_source with rfl | rfl
    · exact universal b (fun same => different same.symm)
    · exact (universal a different).symm
  · exact fun edge => ⟨edge.1.ne, edge.2⟩

/-- The straight source cuts cannot cross away from the common source vertex. -/
theorem source_edge_intersection (P : ConvexPolyhedron) (source a b : P.Vertex)
    (first : P.edgeGraph.Adj source a) (second : P.edgeGraph.Adj source b) (different : a ≠ b) :
    segment ℝ (source : Space) (a : Space) ∩ segment ℝ (source : Space) (b : Space) =
      {(source : Space)} := by
  have edges_different : s(source, a) ≠ s(source, b) := by
    intro same
    rcases Sym2.eq_iff.mp same with ⟨_, equal⟩ | ⟨equal, _⟩
    · exact different equal
    · exact second.ne equal
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨left, right⟩ := P.edge_intersection_is_common_endpoint first second edges_different hx.1 hx.2
    rcases left with at_source | at_a
    · exact at_source
    rcases right with at_source | at_b
    · exact at_source
    · exact False.elim (different (Subtype.ext (at_a.symm.trans at_b)))
  · rintro x rfl
    exact ⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

/-- At a universal source every proposed cut is a shortest continuous surface path along an original edge. -/
theorem universal_source_shortest_cuts (P : ConvexPolyhedron) (source : P.Vertex)
    (universal : ∀ v, v ≠ source → P.edgeGraph.Adj source v) :
    ∀ v, v ≠ source → ∃ path : P.SurfacePath source v, path.IsShortest ∧
      Set.range path.curve = segment ℝ (source : Space) (v : Space) :=
  fun v different => P.edge_has_shortest_surface_path source v (universal v different)

end ConvexPolyhedron
end SixVertexUnfolding
