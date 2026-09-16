import SixVertexUnfolding.Geometry.CutTreeChainRegions
import SixVertexUnfolding.Geometry.FixedFrameChains

/-! The two end kites of any actual simple cut-tree chain are separated
in the single global development already chosen for all its triangles. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Real Wedge

namespace CutTreeChain

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} {n : ℕ}
    (chain : CutTreeChain T n) (charts : CutTreeCharts T)

theorem incoming_kite_global (i : Fin (n + 1)) :
    charts.kite (chain.edge i.castSucc) = charts.frames.frame (chain.vertex i.succ.castSucc) ''
      ((chain.fan charts i).edgeTriangles (chain.edge i.castSucc).symm).developedKite := by
  rw [charts.kite_reverse (chain.edge i.castSucc)]
  exact charts.kite_at_fan _ (charts.internal_nonvertex (chain.edge i.castSucc).symm
    (chain.edge i.succ) (chain.internal_neighbors_different i))

theorem outgoing_kite_global (i : Fin (n + 1)) :
    charts.kite (chain.edge i.succ) = charts.frames.frame (chain.vertex i.succ.castSucc) ''
      ((chain.fan charts i).edgeTriangles (chain.edge i.succ)).developedKite :=
  charts.kite_at_fan _ (charts.internal_nonvertex (chain.edge i.castSucc).symm
    (chain.edge i.succ) (chain.internal_neighbors_different i))

/-- Apply all intermediate moves in their fixed global frames, with the actual end kites. -/
theorem end_kites_nonoverlap (total : (∑ i, chain.sourceAngle charts i) < π) :
    Disjoint (charts.kite (chain.edge 0))
      (interior (charts.kite (chain.edge (Fin.last n).succ))) := by
  classical
  let steps (i : Fin n) : RegionStep (chain.region charts i.castSucc) (chain.region charts i.succ)
      (chain.middleKite charts i) := (chain.region_step charts total i).choose
  have motions (i : Fin n) : (steps i).motion = charts.frames.transition (chain.edge i.succ.castSucc) :=
    (chain.region_step charts total i).choose_spec
  let frames (i : Fin (n + 1)) := charts.frames.frame (chain.vertex i.succ.castSucc)
  have compatible (i : Fin n) (x : Plane) : frames i.succ ((steps i).motion x) = frames i.castSucc x := by
    rw [motions i]
    exact charts.frames.compatible (chain.edge i.succ.castSucc) x
  have result := finite_index_chain_endpoint_separation n (chain.region charts) (chain.middleKite charts)
    steps frames compatible
    ((chain.fan charts 0).edgeTriangles (chain.edge 0).symm).developedKite
    ((chain.fan charts (Fin.last n)).edgeTriangles (chain.edge (Fin.last n).succ)).developedKite
    (chain.first_kite_in_region charts) (chain.region_avoids_outgoing charts total (Fin.last n))
  have first : charts.kite (chain.edge 0) = frames 0 ''
      ((chain.fan charts 0).edgeTriangles (chain.edge 0).symm).developedKite :=
    chain.incoming_kite_global charts 0
  have last := chain.outgoing_kite_global charts (Fin.last n)
  dsimp only [frames] at result
  rw [first, last]
  exact result

end CutTreeChain

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- The source cone discharges every numerical premise of the global chain separation. -/
theorem cut_tree_chain_end_kites_nonoverlap {a : frontier P.body} (T : P.CutLocusTree a)
    (charts : CutTreeCharts T) {n : ℕ} (chain : CutTreeChain T n)
    (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space)) :
    Disjoint (charts.kite (chain.edge 0))
      (interior (charts.kite (chain.edge (Fin.last n).succ))) :=
  chain.end_kites_nonoverlap charts (graph.cut_tree_chain_source_budget small_faces T charts chain source at_source)

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
