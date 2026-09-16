import SixVertexUnfolding.Geometry.StarInverseDisks
import SixVertexUnfolding.Geometry.SmallPolyhedronKiteNeighborhood
import SixVertexUnfolding.Geometry.SmallPolyhedronJunctionInverseDisk
import SixVertexUnfolding.Geometry.SmallPolyhedronJunctionRayInverseDisk

/-! Every retained surface point has an actual inverse disk. The
proof covers triangle interiors, cut-edge bases, retained rays, and junctions.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter Topology

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

theorem small_hasInverseDisk_at_junction {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (separated : charts.KitesSeparated)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (b : P.UncutSurface a) (u : T.vertices) (nonvertex : (u : Space) ∉ P.vertices)
    (at_junction : b.val = T.vertexTarget u) : charts.HasInverseDisk b := by
  let fan := charts.fan u nonvertex
  have outside : T.vertexTarget u ∉ P.starCuts a := at_junction ▸ b.property
  have located : (b.val : Space) = fan.order.chart.map fan.order.chart.origin := by
    rw [fan.order.chart.at_origin]
    exact congrArg (fun c : frontier P.body => (c : Space)) at_junction
  have center_eq := small_develop_fan_chart size small_faces charts cofacial u nonvertex
    fan.order.chart.origin fan.chartPlaces_origin b located
  obtain ⟨radius, positive, inverse, right_inverse, left_inverse, _⟩ :=
    small_exists_junction_inverse_disk size small_faces charts separated cofacial u nonvertex outside
  unfold CutTreeCharts.HasInverseDisk
  rw [center_eq]
  exact ⟨radius, positive, inverse,
    charts.inverse_has_finite_pieces _ (fun x => (inverse x).val) right_inverse,
    right_inverse, left_inverse⟩

theorem small_hasInverseDisk_on_endpoint_ray {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (separated : charts.KitesSeparated)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v : T.vertices} (edge : T.graph.Adj u v) (b : P.UncutSurface a)
    (placed : (charts.global edge).PlacesOnRay 0 b.val (charts.develop b.val)) : charts.HasInverseDisk b := by
  have nonvertex := (charts.global edge).endpoint_nonvertex_of_outside_cuts cofacial b.property placed
  let fan := charts.fan u nonvertex
  let D := fan.edgeTriangles edge
  have local_placement := ((charts.triangles edge).placesOnRay_inFrame (charts.frames.frame u) 0 b.val _).mp placed
  rw [charts.at_fan edge nonvertex] at local_placement
  change D.placed.PlacesOnRay 0 b.val _ at local_placement
  obtain ⟨side, time, at_b, _⟩ := local_placement
  change D.routes side 0 time = b.val at at_b
  have member : D.routes side 0 ∈ P.geodesicFiber a (T.vertexTarget u) := by
    simpa only [T.closedEdgeTarget_zero] using D.routes_member side 0
  have positive : 0 < time := by
    have nonzero : time ≠ 0 := by
      intro zero
      subst time
      have same : b.val = a := at_b.symm.trans (congrArg Prod.fst member.2)
      exact b.property (same.symm ▸ P.source_mem_starCuts a)
    exact lt_of_le_of_ne (show (0 : unitInterval) ≤ time from time.property.1) (Ne.symm nonzero)
  by_cases last : time = 1
  · subst time
    exact small_hasInverseDisk_at_junction size small_faces charts separated cofacial b u nonvertex
      (at_b.symm.trans (congrArg Prod.snd member.2))
  · have before : time < 1 := lt_of_le_of_ne (show time ≤ (1 : unitInterval) from time.property.2) last
    let p : fan.order.chart.sources := ⟨D.motion (D.apex side),
      (fan.order.chart.source_routes _).mpr ⟨D.routes side 0, member, D.route_label side⟩⟩
    have outside : D.routes side 0 time ∉ P.starCuts a := at_b.symm ▸ b.property
    obtain ⟨center_eq, radius, rp, inverse, pieces, right_inverse, left_inverse⟩ :=
      small_exists_junction_ray_inverse_disk size small_faces charts separated cofacial u nonvertex
        p (D.routes side 0) member (D.route_label side) time positive before outside
    rw [at_b] at center_eq
    unfold CutTreeCharts.HasInverseDisk
    rw [center_eq]
    exact ⟨radius, rp, inverse, pieces, right_inverse, left_inverse⟩

/-- All local cases are discharged for the actual cofacial-source development. -/
theorem small_every_retained_point_has_inverse_disk {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (separated : charts.KitesSeparated)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (b : P.UncutSurface a) : charts.HasInverseDisk b := by
  obtain ⟨u, v, edge, actual⟩ := charts.develop_spec b.val
  obtain ⟨s, placed⟩ := ((charts.global edge).places_iff_ray b.val (charts.develop b.val)).mp actual
  by_cases first : s = 0
  · subst s
    exact small_hasInverseDisk_on_endpoint_ray size small_faces charts separated cofacial edge b placed
  by_cases last : s = 1
  · subst s
    have not_source : b.val ≠ a := fun equal => b.property (equal.symm ▸ P.source_mem_starCuts a)
    have reversed := small_global_ray_placement_reverse size small_faces charts edge not_source placed
    have reversed : (charts.global edge.symm).PlacesOnRay 0 b.val (charts.develop b.val) := by
      simpa only [unitInterval.symm_one] using reversed
    exact small_hasInverseDisk_on_endpoint_ray size small_faces charts separated cofacial edge.symm b reversed
  have sp : 0 < s := lt_of_le_of_ne (show (0 : unitInterval) ≤ s from s.property.1) (Ne.symm first)
  have sb : s < 1 := lt_of_le_of_ne (show s ≤ (1 : unitInterval) from s.property.2) last
  obtain ⟨side, time, at_b, position⟩ := placed
  have tp : 0 < time := by
    have nonzero : time ≠ 0 := by
      intro zero
      subst time
      have same : b.val = a := at_b.symm.trans (congrArg Prod.fst ((charts.global edge).routes_member side s).2)
      exact b.property (same.symm ▸ P.source_mem_starCuts a)
    exact lt_of_le_of_ne (show (0 : unitInterval) ≤ time from time.property.1) (Ne.symm nonzero)
  have inside : charts.develop b.val ∈ interior (charts.kite edge) :=
    position ▸ (charts.global edge).interior_ray_in_kite side s time sp sb tp
  exact small_exists_kite_inverse_disk size small_faces charts separated cofacial edge b inside

end SixVertexUnfolding.ConvexPolyhedron
