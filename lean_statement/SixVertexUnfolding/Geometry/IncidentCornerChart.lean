import SixVertexUnfolding.Geometry.TriangleFoldNeighborhood
import SixVertexUnfolding.Geometry.JunctionRayMapAgreement
import SixVertexUnfolding.Geometry.PlacedKiteBase

/-! Each incident radial triangle agrees with the genuine junction
chart on a positive small triangle at the junction. -/

namespace SixVertexUnfolding.ConvexPolyhedron.IncidentTriangles

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v}
    {chart : P.CutVoronoiChart a (T.vertexTarget u)} {angle : ℝ}
    (D : IncidentTriangles T edge chart angle)

/-- Both boundary rays determine the folding on a small filled corner. -/
theorem exists_chart_corner (side : Bool) {radius : ℝ} (positive : 0 < radius)
    (ray : ∀ ρ ∈ Ioo (0 : ℝ) radius,
      chart.map (chart.origin + ρ • direction angle) ∈ openSegment ℝ (u : Space) (v : Space)) :
    ∃ s t : unitInterval, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      let q := AffineMap.lineMap chart.origin (D.motion (D.apex side)) (s : ℝ)
      let r := AffineMap.lineMap chart.origin (D.motion D.model.right) (t : ℝ)
      ∃ contained : convexHull ℝ ({q, chart.origin, r} : Set Plane) ⊆ D.placed.sideRegion side,
        convexHull ℝ ({q, chart.origin, r} : Set Plane) ⊆ chart.domain ∧
        ∀ x : convexHull ℝ ({q, chart.origin, r} : Set Plane),
          (((D.placed.sideTriangle side).homeomorph.symm ⟨x, contained x.property⟩).val : Space) = chart.map x := by
  let H := D.placed.sideTriangle side
  have route_end : (D.routes side 0 1 : Space) = (u : Space) := by
    have endpoint := congrArg Prod.snd (D.routes_member side 0).2
    rw [T.closedEdgeTarget_zero] at endpoint
    exact congrArg (fun b : frontier P.body => (b : Space)) endpoint
  obtain ⟨ε, ep, fold_inside⟩ := H.fold_near_left_in_chart chart.toFlatChart route_end
  obtain ⟨η, hp, chart_disk⟩ := Metric.isOpen_iff.mp chart.open_domain chart.origin chart.origin_mem
  let δ := min ε η
  have dp : 0 < δ := lt_min ep hp
  obtain ⟨start, before, tail⟩ := D.route_label side
  have denominator : 0 < dist chart.origin (D.motion (D.apex side)) + 1 := by positivity
  obtain ⟨s₀, sp, ss⟩ := exists_between (lt_min (show (0 : ℝ) < 1 - (start : ℝ) by exact sub_pos.mpr before)
    (div_pos dp denominator))
  have s_one : s₀ < 1 := by linarith [start.property.1, ss.trans_le (min_le_left _ _)]
  let s : unitInterval := ⟨s₀, sp.le, s_one.le⟩
  let q := AffineMap.lineMap chart.origin (D.motion (D.apex side)) (s : ℝ)
  have q_near : dist q chart.origin < δ := by
    rw [dist_lineMap_left, Real.norm_of_nonneg s.property.1]
    have short := (lt_div_iff₀ denominator).mp (ss.trans_le (min_le_right _ _))
    change s₀ * dist chart.origin (D.motion (D.apex side)) < δ
    nlinarith
  have edge_denominator : 0 < dist (u : Space) (v : Space) + 1 := by positivity
  obtain ⟨t, tp, t_one, t_short, _, r_domain, r_mapped⟩ := chart.incident_edge_sample T edge rfl
    positive (div_pos dp edge_denominator) ray
  let r := AffineMap.lineMap chart.origin (D.motion D.model.right) (t : ℝ)
  have r_formula : r = chart.origin + ((t : ℝ) * dist (u : Space) (v : Space)) • direction angle := by
    dsimp [r]
    rw [D.at_neighbor, AffineMap.lineMap_apply_module]
    module
  have r_near : dist r chart.origin < δ := by
    rw [r_formula, dist_eq_norm, add_sub_cancel_left, norm_smul, direction_norm, mul_one,
      Real.norm_of_nonneg (mul_nonneg t.property.1 dist_nonneg)]
    have short := (lt_div_iff₀ edge_denominator).mp t_short
    have t_positive : (0 : ℝ) < t := tp
    nlinarith
  have root_in : chart.origin ∈ D.placed.sideRegion side := by
    rw [← D.at_junction]
    exact subset_convexHull ℝ _ (Or.inr (Or.inl rfl))
  have source_in : D.motion (D.apex side) ∈ D.placed.sideRegion side := subset_convexHull ℝ _ (Or.inl rfl)
  have neighbor_in : D.motion D.model.right ∈ D.placed.sideRegion side := subset_convexHull ℝ _ (Or.inr (Or.inr rfl))
  have q_in : q ∈ D.placed.sideRegion side :=
    (convex_convexHull ℝ _).mapsTo_lineMap root_in source_in s.property
  have r_in : r ∈ D.placed.sideRegion side :=
    (convex_convexHull ℝ _).mapsTo_lineMap root_in neighbor_in t.property
  let corners : Set Plane := {q, chart.origin, r}
  have corners_in : corners ⊆ D.placed.sideRegion side := by
    intro x hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have contained : convexHull ℝ corners ⊆ D.placed.sideRegion side :=
    convexHull_min corners_in (convex_convexHull ℝ _)
  have in_ball : convexHull ℝ corners ⊆ Metric.ball chart.origin δ :=
    convexHull_min (by
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact q_near
      · exact Metric.mem_ball_self dp
      · exact r_near) (convex_ball _ _)
  have in_domain : convexHull ℝ corners ⊆ chart.domain := fun x hx =>
    chart_disk ((Metric.mem_ball.mp (in_ball hx)).trans_le (min_le_right _ _))
  have in_chart (x : convexHull ℝ corners) :
      ((H.homeomorph.symm ⟨x, contained x.property⟩).val : Space) ∈ chart.map '' chart.domain := by
    apply fold_inside
    change dist (x : Plane) (D.motion D.model.left) < ε
    rw [D.at_junction]
    exact (Metric.mem_ball.mp (in_ball x.property)).trans_le (min_le_left _ _)
  have q_fold : ((H.homeomorph.symm ⟨q, q_in⟩).val : Space) = chart.map q := by
    let time := unitInterval.symm s
    have time_after : time ∈ Icc start 1 := by
      refine ⟨?_, time.property.2⟩
      change (start : ℝ) ≤ 1 - s₀
      linarith [ss.trans_le (min_le_left _ _)]
    have placed : (H.homeomorph ⟨closedRouteStripMap (D.routes side) (0, time), mem_range_self _⟩ : Plane) = q := by
      apply (H.radial (0, time)).trans
      change AffineMap.lineMap (D.motion (D.apex side))
        (AffineMap.lineMap (D.motion D.model.left) (D.motion D.model.right) 0) (1 - (s : ℝ)) = q
      rw [AffineMap.lineMap_apply_zero, D.at_junction, AffineMap.lineMap_apply_one_sub]
    have point : H.homeomorph ⟨closedRouteStripMap (D.routes side) (0, time), mem_range_self _⟩ = ⟨q, q_in⟩ := Subtype.ext placed
    have inverse := congrArg H.homeomorph.symm point
    rw [H.homeomorph.symm_apply_apply] at inverse
    have tail_agrees := (tail time time_after).2
    change chart.map (AffineMap.lineMap (D.motion (D.apex side)) chart.origin (1 - (s : ℝ))) = _ at tail_agrees
    rw [AffineMap.lineMap_apply_one_sub] at tail_agrees
    exact (congrArg (fun x : range (closedRouteStripMap (D.routes side)) => (x.val : Space)) inverse).symm.trans tail_agrees.symm
  have root_fold : ((H.homeomorph.symm ⟨chart.origin, root_in⟩).val : Space) = chart.map chart.origin := by
    rw [chart.at_origin]
    exact (congrArg (fun b : frontier P.body => (b : Space))
      (H.fold_left_corner ⟨chart.origin, root_in⟩ D.at_junction.symm)).trans route_end
  have r_fold : ((H.homeomorph.symm ⟨r, r_in⟩).val : Space) = chart.map r := by
    have base : AffineMap.lineMap (D.motion D.model.left) (D.motion D.model.right) (t : ℝ) = r := by
      rw [D.at_junction]
    have folded := D.placed.fold_on_base side t (base.symm ▸ r_in)
    have located : chart.map r = (T.closedEdgeTarget edge t : Space) := by simpa only [r_formula] using r_mapped
    have same_point : (⟨AffineMap.lineMap (D.motion D.model.left) (D.motion D.model.right) (t : ℝ), base.symm ▸ r_in⟩ : D.placed.sideRegion side) = ⟨r, r_in⟩ := Subtype.ext base
    have same_fold := congrArg (fun x : D.placed.sideRegion side => ((H.homeomorph.symm x).val : Space)) same_point
    exact same_fold.symm.trans ((congrArg (fun b : frontier P.body => (b : Space)) folded).trans located.symm)
  refine ⟨s, t, sp, s_one, tp, t_one, contained, in_domain, ?_⟩
  apply H.fold_eq_chart_on_hull chart.toFlatChart corners contained in_chart
    (fun x hx => in_domain (subset_convexHull ℝ _ hx))
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact q_fold
  · exact root_fold
  · exact r_fold

end SixVertexUnfolding.ConvexPolyhedron.IncidentTriangles
