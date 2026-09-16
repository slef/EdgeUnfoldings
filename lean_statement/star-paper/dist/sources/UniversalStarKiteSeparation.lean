import SixVertexUnfolding.Geometry.SmallPolyhedronSourceBudget
import SixVertexUnfolding.Geometry.SmallPolyhedronCutTreeCharts
import SixVertexUnfolding.Geometry.CutTreeChainPaths

/-! Global kite separation for the six-vertex universal-source star.
Every kite is placed in the same fixed plane; its angle budget has been
proved from the original faces rather than a prescribed graph model. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Real

variable {P : ConvexPolyhedron} (six : P.vertices.card = 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  {a : frontier P.body} (T : P.CutLocusTree a) (charts : CutTreeCharts T)
  (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v)
  (at_source : (a : Space) = (source : Space))

include six small_faces universal at_source in
/-- Every simple chain fits within the actual source-angle budget. -/
theorem universal_cut_tree_chain_source_budget {n : ℕ} (chain : CutTreeChain T n) :
    (∑ i, chain.sourceAngle charts i) < π := by
  classical
  letI : Fintype P.Face := Fintype.ofFinite P.Face
  letI : Fintype T.vertices := T.finite_vertices.fintype
  letI : DecidableRel T.graph.Adj := Classical.decRel _
  let models (d : T.graph.Dart) := (charts.triangles d.adj).model
  let selected := Finset.univ.image chain.dart
  have no_reverse : ∀ d ∈ selected, d.symm ∉ selected := by
    rintro d member reverse
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp member
    obtain ⟨j, _, same⟩ := Finset.mem_image.mp reverse
    exact chain.dart_ne_reverse i j same.symm
  have bound := (T.selected_source_angle_sum_le_half models selected no_reverse).trans_lt
    (universal_half_source_angle_sum_lt_pi small_faces T models six source universal at_source)
  have sum_eq : (∑ d ∈ selected, (models d).sourceAngle) = ∑ i, chain.sourceAngle charts i := by
    rw [Finset.sum_image]
    · rfl
    · exact fun _ _ _ _ same => chain.dart_injective same
  rwa [sum_eq] at bound

include six small_faces universal at_source in
/-- Distinct actual tree-edge kites have disjoint interiors in the common development. -/
theorem universal_global_kites_nonoverlap
    {u v w z : T.vertices} (first : T.graph.Adj u v) (last : T.graph.Adj w z)
    (different : s(u, v) ≠ s(w, z)) :
    Disjoint (charts.kite first) (interior (charts.kite last)) := by
  obtain ⟨n, chain, first_same, last_same⟩ := T.exists_chain_between_edges first last different
  have first_image : charts.kite (chain.edge 0) = charts.kite first :=
    charts.kite_eq_of_same_edge _ first first_same
  have last_image : charts.kite (chain.edge (Fin.last n).succ) = charts.kite last :=
    charts.kite_eq_of_same_edge _ last last_same
  rw [← first_image, ← last_image]
  exact chain.end_kites_nonoverlap charts
    (universal_cut_tree_chain_source_budget six small_faces T charts source universal at_source chain)

include six small_faces universal at_source in
/-- Construct the full covering chart collection with every pair of kites separated. -/
theorem universal_exists_separated_cut_tree_charts :
    ∃ charts : CutTreeCharts T,
      ∀ {u v w z : T.vertices} (first : T.graph.Adj u v) (last : T.graph.Adj w z),
        s(u, v) ≠ s(w, z) → Disjoint (charts.kite first) (interior (charts.kite last)) := by
  obtain ⟨charts⟩ := small_universal_source_cut_tree_charts (show P.vertices.card ≤ 6 by omega)
    small_faces a source at_source universal T
  exact ⟨charts, fun first last different =>
    universal_global_kites_nonoverlap six small_faces T charts source universal at_source first last different⟩

end SixVertexUnfolding.ConvexPolyhedron
