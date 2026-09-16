import SixVertexUnfolding.Geometry.GlobalCutTreeKites
import SixVertexUnfolding.Geometry.CutTreePathBudget

/-! A simple finite chain of actual tree edges. The first and last
edges are the kites to be separated; all intervening junctions use
the fixed global chart collection. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Real

/-- A simple chain with two end edges and `n` intermediate edges. -/
structure CutTreeChain {P : ConvexPolyhedron} {a : frontier P.body}
    (T : P.CutLocusTree a) (n : ℕ) where
  vertex : Fin (n + 3) → T.vertices
  simple : Function.Injective vertex
  edge : ∀ i : Fin (n + 2), T.graph.Adj (vertex i.castSucc) (vertex i.succ)

namespace CutTreeChain

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} {n : ℕ}
    (chain : CutTreeChain T n)

def dart (i : Fin (n + 2)) : T.graph.Dart :=
  ⟨(chain.vertex i.castSucc, chain.vertex i.succ), chain.edge i⟩

theorem dart_injective : Function.Injective chain.dart := by
  intro i j same
  have first : chain.vertex i.castSucc = chain.vertex j.castSucc :=
    congrArg (fun d : T.graph.Dart => d.fst) same
  exact Fin.ext (congrArg (fun k : Fin (n + 3) => k.val) (chain.simple first))

theorem dart_ne_reverse (i j : Fin (n + 2)) : (chain.dart i).symm ≠ chain.dart j := by
  intro same
  have first : chain.vertex i.succ = chain.vertex j.castSucc :=
    congrArg (fun d : T.graph.Dart => d.fst) same
  have second : chain.vertex i.castSucc = chain.vertex j.succ :=
    congrArg (fun d : T.graph.Dart => d.snd) same
  have h₁ := congrArg Fin.val (chain.simple first)
  have h₂ := congrArg Fin.val (chain.simple second)
  simp only [Fin.val_succ, Fin.val_castSucc] at h₁ h₂
  omega

theorem internal_neighbors_different (i : Fin (n + 1)) :
    chain.vertex i.castSucc.castSucc ≠ chain.vertex i.succ.succ := by
  intro same
  have indices := congrArg Fin.val (chain.simple same)
  simp only [Fin.val_succ, Fin.val_castSucc] at indices
  omega

/-- Each internal fan is selected from the one fixed chart collection. -/
noncomputable def fan (charts : CutTreeCharts T) (i : Fin (n + 1)) :
    JunctionFan T (chain.vertex i.succ.castSucc) :=
  charts.fan _ (charts.internal_nonvertex (chain.edge i.castSucc).symm
    (chain.edge i.succ) (chain.internal_neighbors_different i))

/-- The source angle charged for this actual edge, in the fixed chart collection. -/
noncomputable def sourceAngle (charts : CutTreeCharts T) (i : Fin (n + 2)) : ℝ :=
  (charts.triangles (chain.edge i)).model.sourceAngle

theorem sourceAngle_pos (charts : CutTreeCharts T) (i : Fin (n + 2)) :
    0 < chain.sourceAngle charts i := (charts.triangles (chain.edge i)).model.sourceAngle_pos

/-- The accumulated source angle before the edge with numerical index `k`. -/
noncomputable def angleBefore (charts : CutTreeCharts T) (k : ℕ) : ℝ :=
  ∑ i : Fin (n + 2) with i.val < k, chain.sourceAngle charts i

theorem angleBefore_zero (charts : CutTreeCharts T) : chain.angleBefore charts 0 = 0 := by
  simp [angleBefore]

theorem angleBefore_nonneg (charts : CutTreeCharts T) (k : ℕ) : 0 ≤ chain.angleBefore charts k :=
  Finset.sum_nonneg (fun i _ => (chain.sourceAngle_pos charts i).le)

theorem angleBefore_le_total (charts : CutTreeCharts T) (k : ℕ) :
    chain.angleBefore charts k ≤ ∑ i, chain.sourceAngle charts i :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => (chain.sourceAngle_pos charts i).le)

/-- Extending the prefix charges precisely the next actual kite angle. -/
theorem angleBefore_succ (charts : CutTreeCharts T) (i : Fin (n + 2)) :
    chain.angleBefore charts (i.val + 1) = chain.angleBefore charts i.val + chain.sourceAngle charts i := by
  classical
  have next : (Finset.univ.filter (fun j : Fin (n + 2) => j.val < i.val + 1)) =
      insert i (Finset.univ.filter (fun j : Fin (n + 2) => j.val < i.val)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro small
      by_cases same : j.val = i.val
      · exact Or.inl (Fin.ext same)
      · exact Or.inr (by omega)
    · rintro (rfl | smaller) <;> omega
  have absent : i ∉ Finset.univ.filter (fun j : Fin (n + 2) => j.val < i.val) := by simp
  simp only [angleBefore]
  rw [next, Finset.sum_insert absent]
  ring

end CutTreeChain

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- The actual source cone bounds the sum along every simple finite chain. -/
theorem cut_tree_chain_source_budget {a : frontier P.body} (T : P.CutLocusTree a)
    (charts : CutTreeCharts T) {n : ℕ} (chain : CutTreeChain T n)
    (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space)) :
    (∑ i, chain.sourceAngle charts i) < π := by
  classical
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
    (graph.half_source_angle_sum_lt_pi small_faces T models source at_source)
  have sum_eq : (∑ d ∈ selected, (models d).sourceAngle) = ∑ i, chain.sourceAngle charts i := by
    rw [Finset.sum_image]
    · rfl
    · exact fun _ _ _ _ same => chain.dart_injective same
  rwa [sum_eq] at bound

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
