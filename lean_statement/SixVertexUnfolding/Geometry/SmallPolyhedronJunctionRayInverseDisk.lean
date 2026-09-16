import SixVertexUnfolding.Geometry.JunctionRayInverseDisk
import SixVertexUnfolding.Geometry.SmallPolyhedronJunctionRayFolding
import SixVertexUnfolding.Geometry.SmallPolyhedronFoldingInverseDisk

/-! The two actual triangles adjoining each retained junction ray
supply a true inverse disk at every point of its open length.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

theorem small_exists_junction_ray_inverse_disk {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (separated : charts.KitesSeparated)
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
    fan.small_exists_source_ray_folding size small_faces p route member represented frame
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
    exact small_develop_agrees size small_faces charts cofacial edge uncut global
  have retained : fold point ∉ P.starCuts a := folds.symm ▸ outside
  refine ⟨?_, small_exists_folding_inverse_disk size small_faces charts separated cofacial
    region fold pieces point inside retained develops⟩
  exact folds ▸ develops point retained

end SixVertexUnfolding.ConvexPolyhedron
