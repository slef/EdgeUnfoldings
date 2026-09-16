import SixVertexUnfolding.Geometry.CutTreeChains
import SixVertexUnfolding.Geometry.FixedFanWedgeStep

/-! The growing regions of an actual simple tree chain. Their angles
are the exact accumulated source angles, and their motions are those
already fixed for the whole chart collection. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutTreeChain

open Set Real Wedge

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} {n : ℕ}
    (chain : CutTreeChain T n) (charts : CutTreeCharts T)

theorem fan_triangles (i : Fin (n + 1)) {v : T.vertices}
    (edge : T.graph.Adj (chain.vertex i.succ.castSucc) v) :
    charts.triangles edge = ((chain.fan charts i).edgeTriangles edge).placed :=
  charts.at_fan edge _

theorem outgoing_sourceAngle (i : Fin (n + 1)) :
    ((chain.fan charts i).edgeTriangles (chain.edge i.succ)).model.sourceAngle =
      chain.sourceAngle charts i.succ := by
  unfold sourceAngle
  rw [chain.fan_triangles charts i (chain.edge i.succ)]
  rfl

theorem incoming_sourceAngle (i : Fin (n + 1)) :
    ((chain.fan charts i).edgeTriangles (chain.edge i.castSucc).symm).model.sourceAngle =
      chain.sourceAngle charts i.castSucc :=
  ((charts.triangles (chain.edge i.castSucc)).model.reverse_angles
    ((chain.fan charts i).edgeTriangles (chain.edge i.castSucc).symm).model).1.symm

noncomputable def outerAngle (i : Fin (n + 1)) : ℝ :=
  π / 2 + chain.angleBefore charts (i.val + 1)

noncomputable def region (i : Fin (n + 1)) : Set Plane :=
  ((chain.fan charts i).edgeTriangles (chain.edge i.castSucc).symm).incomingWedge
    (chain.outerAngle charts i)

noncomputable def middleKite (i : Fin n) : Set Plane :=
  ((chain.fan charts i.castSucc).edgeTriangles (chain.edge i.succ.castSucc)).developedKite

theorem outerAngle_lower (i : Fin (n + 1)) : π / 2 ≤ chain.outerAngle charts i :=
  le_add_of_nonneg_right (chain.angleBefore_nonneg charts _)

theorem outerAngle_budget (total : (∑ i, chain.sourceAngle charts i) < π) (i : Fin (n + 1)) :
    chain.outerAngle charts i + chain.sourceAngle charts i.succ < 3 * π / 2 := by
  have bound := (chain.angleBefore_le_total charts (i.val + 2)).trans_lt total
  have update := chain.angleBefore_succ charts i.succ
  change chain.angleBefore charts (i.val + 2) =
    chain.angleBefore charts (i.val + 1) + chain.sourceAngle charts i.succ at update
  rw [update] at bound
  change π / 2 + chain.angleBefore charts (i.val + 1) + chain.sourceAngle charts i.succ < _
  linarith

theorem outerAngle_step (i : Fin n) :
    chain.outerAngle charts i.castSucc +
      ((chain.fan charts i.castSucc).edgeTriangles (chain.edge i.succ.castSucc)).model.sourceAngle =
        chain.outerAngle charts i.succ := by
  have same_angle : ((chain.fan charts i.castSucc).edgeTriangles
      (chain.edge i.succ.castSucc)).model.sourceAngle = chain.sourceAngle charts i.succ.castSucc := by
    simpa only [Fin.succ_castSucc] using chain.outgoing_sourceAngle charts i.castSucc
  rw [same_angle]
  have update := chain.angleBefore_succ charts i.succ.castSucc
  change chain.angleBefore charts (i.val + 2) =
    chain.angleBefore charts (i.val + 1) + chain.sourceAngle charts i.succ.castSucc at update
  change π / 2 + chain.angleBefore charts (i.val + 1) + chain.sourceAngle charts i.succ.castSucc =
    π / 2 + chain.angleBefore charts (i.val + 2)
  linarith

/-- The first actual kite is enclosed with exactly its own source-angle charge. -/
theorem first_kite_in_region :
    ((chain.fan charts 0).edgeTriangles (chain.edge 0).symm).developedKite ⊆ chain.region charts 0 := by
  have charge : chain.angleBefore charts 1 = chain.sourceAngle charts 0 := by
    simpa only [Fin.val_zero, zero_add, chain.angleBefore_zero charts] using chain.angleBefore_succ charts 0
  change _ ⊆ ((chain.fan charts 0).edgeTriangles (chain.edge 0).symm).incomingWedge
    (π / 2 + chain.angleBefore charts 1)
  have angle := chain.incoming_sourceAngle charts 0
  simp only [Fin.castSucc_zero] at angle
  rw [charge, ← angle]
  exact ((chain.fan charts 0).edgeTriangles (chain.edge 0).symm).initial_kite_in_wedge

/-- At any internal junction the incoming region excludes the next actual kite. -/
theorem region_avoids_outgoing (total : (∑ i, chain.sourceAngle charts i) < π) (i : Fin (n + 1)) :
    Disjoint (chain.region charts i)
      (interior ((chain.fan charts i).edgeTriangles (chain.edge i.succ)).developedKite) := by
  apply (chain.fan charts i).edge_wedge_avoids_kite (chain.edge i.castSucc).symm (chain.edge i.succ)
    (chain.internal_neighbors_different i) _ (chain.outerAngle_lower charts i)
  rw [chain.outgoing_sourceAngle charts i]
  exact (chain.outerAngle_budget charts total i).le

/-- Every intermediate step uses the transition already chosen for the whole tree. -/
theorem region_step (total : (∑ i, chain.sourceAngle charts i) < π) (i : Fin n) :
    ∃ step : RegionStep (chain.region charts i.castSucc) (chain.region charts i.succ)
      (chain.middleKite charts i), step.motion = charts.frames.transition (chain.edge i.succ.castSucc) := by
  let first := chain.fan charts i.castSucc
  let second := chain.fan charts i.succ
  let incoming := (chain.edge i.castSucc.castSucc).symm
  let outgoing := chain.edge i.succ.castSucc
  have distinct := chain.internal_neighbors_different i.castSucc
  have roots := charts.transition_at_fans outgoing
    (charts.internal_nonvertex incoming outgoing distinct)
    (charts.internal_nonvertex outgoing.symm (chain.edge i.succ.succ)
      (chain.internal_neighbors_different i.succ))
  have budget : chain.outerAngle charts i.castSucc +
      (first.edgeTriangles outgoing).model.sourceAngle ≤ 3 * π / 2 := by
    have same_angle : (first.edgeTriangles outgoing).model.sourceAngle =
        chain.sourceAngle charts i.succ.castSucc := by
      simpa only [first, outgoing, Fin.succ_castSucc] using chain.outgoing_sourceAngle charts i.castSucc
    rw [same_angle]
    simpa only [Fin.succ_castSucc] using (chain.outerAngle_budget charts total i.castSucc).le
  have result := first.edge_region_step_with_motion incoming outgoing distinct second
    (chain.outerAngle charts i.castSucc) (chain.outerAngle_lower charts i.castSucc) budget
    (charts.frames.transition outgoing) roots.1 roots.2
  have angle := chain.outerAngle_step charts i
  change chain.outerAngle charts i.castSucc + (first.edgeTriangles outgoing).model.sourceAngle =
    chain.outerAngle charts i.succ at angle
  rw [angle] at result
  exact result

end SixVertexUnfolding.ConvexPolyhedron.CutTreeChain
