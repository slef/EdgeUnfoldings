import SixVertexUnfolding.Geometry.JunctionChartPlacement
import SixVertexUnfolding.Geometry.UncutFlatDisk
import SixVertexUnfolding.Geometry.KiteLocalInverse

/-! Every retained nonvertex junction has a true inverse disk for
the global star development, preserving the intrinsic surface metric. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

theorem exists_junction_inverse_disk {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (u : T.vertices) (nonvertex : (u : Space) ∉ P.vertices) (outside : T.vertexTarget u ∉ P.starCuts a) :
    let center := charts.frames.frame u (charts.fan u nonvertex).order.chart.origin
    ∃ radius > 0, ∃ inverse : C(Metric.ball center radius, P.UncutSurface a),
      (∀ x, charts.develop (inverse x).val = x.val) ∧
      (∀ (b : P.UncutSurface a) (inside : charts.develop b.val ∈ Metric.ball center radius),
        inverse ⟨charts.develop b.val, inside⟩ = b) ∧
      (∀ x y, P.surfaceDist (inverse x).val (inverse y).val = dist (x : Plane) (y : Plane)) := by
  let fan := charts.fan u nonvertex
  let chart := fan.order.chart
  let frame := charts.frames.frame u
  obtain ⟨ε, ep, disk⟩ := fan.exists_chart_disk
  obtain ⟨δ, dp, in_domain, uncut⟩ := chart.toFlatChart.exists_uncut_disk a (T.vertexTarget u) rfl outside
  let radius := min ε δ
  have rp : 0 < radius := lt_min ep dp
  have local_small (x : Metric.ball (frame chart.origin) radius) :
      dist (frame.symm (x : Plane)) chart.origin < radius := by
    rw [← frame.dist_map, frame.apply_symm_apply]
    exact x.property
  have domain_member (x : Metric.ball (frame chart.origin) radius) : frame.symm (x : Plane) ∈ chart.domain :=
    in_domain ((local_small x).trans_le (min_le_right _ _))
  have retained (x : Metric.ball (frame chart.origin) radius) :
      (⟨chart.map (frame.symm (x : Plane)), chart.on_surface (domain_member x)⟩ : frontier P.body) ∉ P.starCuts a :=
    uncut ⟨frame.symm x, (local_small x).trans_le (min_le_right _ _)⟩
  let inverse : C(Metric.ball (frame chart.origin) radius, P.UncutSurface a) :=
    ⟨fun x => ⟨⟨chart.map (frame.symm x), chart.on_surface (domain_member x)⟩, retained x⟩,
      ((chart.continuous.comp (frame.symm.continuous.comp continuous_subtype_val)).subtype_mk _).subtype_mk _⟩
  have right_inverse (x : Metric.ball (frame chart.origin) radius) :
      charts.develop (inverse x).val = (x : Plane) := by
    have agrees := graph.develop_fan_chart small_faces charts cofacial u nonvertex (frame.symm x)
      (disk _ ((local_small x).trans_le (min_le_left _ _))) (inverse x) rfl
    exact agrees.trans (frame.apply_symm_apply x)
  refine ⟨radius, rp, inverse, right_inverse, ?_, ?_⟩
  · let development : C(P.UncutSurface a, Plane) :=
      ⟨fun b => charts.develop b.val, graph.develop_continuous small_faces charts cofacial⟩
    exact local_inverse_of_dense_unique development charts.triangleInteriorPoints
      (graph.triangle_interior_points_dense small_faces charts)
      (graph.develop_unique_on_dense_interiors small_faces charts source at_source cofacial)
      (Metric.ball (frame chart.origin) radius) Metric.isOpen_ball inverse right_inverse
  · intro x y
    change P.surfaceDist (chart.map (frame.symm x)) (chart.map (frame.symm y)) = _
    rw [chart.distance _ (domain_member x) _ (domain_member y)]
    exact frame.symm.dist_map x y

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
