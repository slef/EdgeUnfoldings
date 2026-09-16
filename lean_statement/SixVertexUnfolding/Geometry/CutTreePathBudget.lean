import SixVertexUnfolding.Geometry.CutTreeSourceBudget

/-! A simple path uses each unoriented tree edge at most once. Its source
angles therefore fit inside the proved total kite-angle budget. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutLocusTree

open Set Real

variable {P : ConvexPolyhedron} {a : frontier P.body} (T : P.CutLocusTree a)
    [Fintype T.vertices] [DecidableRel T.graph.Adj]
    (models : (d : T.graph.Dart) → CutEdgeMetricModel T d.adj)

/-- An oriented selection with no reversed pair counts at most half the directed total. -/
theorem selected_source_angle_sum_le_half (s : Finset T.graph.Dart)
    (no_reverse : ∀ d ∈ s, d.symm ∉ s) :
    (∑ d ∈ s, (models d).sourceAngle) ≤ (∑ d, (models d).sourceAngle) / 2 := by
  classical
  let reverse := s.image SimpleGraph.Dart.symm
  have disjoint : Disjoint s reverse := by
    apply Finset.disjoint_left.mpr
    intro d ds dr
    obtain ⟨e, es, same⟩ := Finset.mem_image.mp dr
    exact no_reverse e es (same ▸ ds)
  have reversed_sum : (∑ d ∈ reverse, (models d).sourceAngle) = ∑ d ∈ s, (models d).sourceAngle := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro d _
      exact ((models d).reverse_angles (models d.symm)).1.symm
    · intro d _ e _ same
      exact congrArg SimpleGraph.Dart.symm same
  have both : (∑ d ∈ s ∪ reverse, (models d).sourceAngle) ≤ ∑ d, (models d).sourceAngle :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun d _ _ => (models d).sourceAngle_pos.le)
  rw [Finset.sum_union disjoint, reversed_sum] at both
  linarith

omit [Fintype T.vertices] [DecidableRel T.graph.Adj] in
/-- A path cannot contain both orientations of the same edge. -/
theorem path_darts_no_reverse {u v : T.vertices} (path : T.graph.Walk u v) (simple : path.IsPath) :
    ∀ d ∈ path.darts.toFinset, d.symm ∉ path.darts.toFinset := by
  intro d member reverse
  have unique := List.inj_on_of_nodup_map simple.isTrail.edges_nodup
  have same : d.symm = d := unique (List.mem_toFinset.mp reverse)
    (List.mem_toFinset.mp member) d.edge_symm
  exact d.symm_ne same

/-- The finite sum over any simple path is bounded by the total of all kites. -/
theorem path_source_angle_sum_le_half {u v : T.vertices}
    (path : T.graph.Walk u v) (simple : path.IsPath) :
    (∑ d ∈ path.darts.toFinset, (models d).sourceAngle) ≤ (∑ d, (models d).sourceAngle) / 2 :=
  T.selected_source_angle_sum_le_half models path.darts.toFinset (T.path_darts_no_reverse path simple)

end SixVertexUnfolding.ConvexPolyhedron.CutLocusTree

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    {a : frontier P.body} (T : P.CutLocusTree a)
    [Fintype T.vertices] [DecidableRel T.graph.Adj]
    (models : (d : T.graph.Dart) → CutEdgeMetricModel T d.adj)

include small_faces in
/-- Every simple tree path has cumulative source angle strictly below π. -/
theorem path_source_angle_sum_lt_pi (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space))
    {u v : T.vertices} (path : T.graph.Walk u v) (simple : path.IsPath) :
    (∑ d ∈ path.darts.toFinset, (models d).sourceAngle) < π :=
  (T.path_source_angle_sum_le_half models path simple).trans_lt
    (graph.half_source_angle_sum_lt_pi small_faces T models source at_source)

include small_faces in
/-- The outer angle obtained from any simple path stays inside the wedge step's range. -/
theorem path_outer_angle_bounds (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space))
    {u v : T.vertices} (path : T.graph.Walk u v) (simple : path.IsPath) :
    π / 2 ≤ π / 2 + (∑ d ∈ path.darts.toFinset, (models d).sourceAngle) ∧
      π / 2 + (∑ d ∈ path.darts.toFinset, (models d).sourceAngle) < 3 * π / 2 := by
  have nonnegative : 0 ≤ ∑ d ∈ path.darts.toFinset, (models d).sourceAngle :=
    Finset.sum_nonneg (fun d _ => (models d).sourceAngle_pos.le)
  have bound := graph.path_source_angle_sum_lt_pi small_faces T models source at_source path simple
  constructor <;> linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
