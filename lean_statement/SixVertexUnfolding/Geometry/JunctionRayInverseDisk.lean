import SixVertexUnfolding.Geometry.JunctionRayFolding
import SixVertexUnfolding.Geometry.GlobalFanPlacement
import SixVertexUnfolding.Geometry.FoldingInverseDisk

/-! The two actual triangles adjoining each retained junction ray
supply a true inverse disk at every point of its open length. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

theorem exists_junction_ray_inverse_disk {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (u : T.vertices) (nonvertex : (u : Space) ∉ P.vertices)
    (p : (charts.fan u nonvertex).order.chart.sources) (route : P.BoundaryCurve)
    (member : route ∈ P.geodesicFiber a (T.vertexTarget u))
    (represented : (charts.fan u nonvertex).order.chart.Represents p route)
    (t : unitInterval) (positive : 0 < t) (before : t < 1) (outside : route t ∉ P.starCuts a) :
    let frame := charts.frames.frame u
    let center := AffineMap.lineMap (frame p) (frame (charts.fan u nonvertex).order.chart.origin) (t : ℝ)
    charts.develop (route t) = center ∧
      ∃ radius > 0, ∃ inverse : C(Metric.ball center radius, P.UncutSurface a),
        HasFiniteRigidPieces (Metric.ball center radius) (fun x => ((inverse x).val : Space)) ∧
        (∀ x, charts.develop (inverse x).val = x.val) ∧
        (∀ (b : P.UncutSurface a) (inside : charts.develop b.val ∈ Metric.ball center radius),
          inverse ⟨charts.develop b.val, inside⟩ = b) := by
  let fan := charts.fan u nonvertex
  let frame := charts.frames.frame u
  let center := AffineMap.lineMap (frame p) (frame fan.order.chart.origin) (t : ℝ)
  obtain ⟨region, fold, pieces, interior_ray, placed, on_ray⟩ :=
    fan.exists_source_ray_folding graph small_faces p route member represented frame
  have in_ray : center ∈ openSegment ℝ (frame p) (frame fan.order.chart.origin) := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨t, ⟨positive, before⟩, rfl⟩
  have inside := interior_ray in_ray
  let point : region := ⟨center, interior_subset inside⟩
  have folds : fold point = route t := on_ray t point.property
  have develops (x : region) (uncut : fold x ∉ P.starCuts a) : charts.develop (fold x) = x.val := by
    obtain ⟨m, actual⟩ := placed x
    obtain ⟨v, edge, global⟩ := charts.places_from_fan u nonvertex m (fold x) (frame.symm x) actual
    rw [frame.apply_symm_apply] at global
    exact graph.develop_agrees small_faces charts cofacial edge uncut global
  have retained : fold point ∉ P.starCuts a := folds.symm ▸ outside
  refine ⟨?_, graph.exists_folding_inverse_disk small_faces charts source at_source cofacial
    region fold pieces point inside retained develops⟩
  exact folds ▸ develops point retained

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
