import SixVertexUnfolding.Geometry.StarFlatDiskMetric
import SixVertexUnfolding.Geometry.FlatCoordinateNeighborhood

/-! The cofacial-source star development is locally an isometry for
the actual intrinsic surface distance at every retained point. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

/-- Each retained point has an actual surface neighborhood on which all distances are preserved. -/
theorem develop_locally_isometric {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (b : P.UncutSurface a) :
    ∃ radius > 0, ∀ c d : P.UncutSurface a,
      dist (c.val : Space) (b.val : Space) < radius →
      dist (d.val : Space) (b.val : Space) < radius →
      dist (charts.develop c.val) (charts.develop d.val) = P.surfaceDist c.val d.val := by
  have nonvertex : (b.val : Space) ∉ P.vertices := by
    intro original
    exact b.property ⟨⟨b.val, original⟩, right_mem_segment ℝ _ _⟩
  obtain ⟨flat⟩ := P.exists_flat_chart b.val.property nonvertex
  obtain ⟨ε, ep, contained, inclusion, located, rigid⟩ :=
    graph.develop_isometric_on_small_flat_disk small_faces charts source at_source cofacial b flat
  obtain ⟨radius, positive, near⟩ := flat.exists_coordinate_neighborhood b.val rfl ep
  refine ⟨radius, positive, ?_⟩
  intro c d c_near d_near
  have c_chart := near c.val c_near
  have d_chart := near d.val d_near
  let x : Metric.ball flat.origin ε := ⟨flat.coordinates c.val, c_chart.2⟩
  let y : Metric.ball flat.origin ε := ⟨flat.coordinates d.val, d_chart.2⟩
  have at_c : inclusion x = c := by
    apply Subtype.ext
    exact Subtype.ext ((located x).trans (flat.map_coordinates c_chart.1))
  have at_d : inclusion y = d := by
    apply Subtype.ext
    exact Subtype.ext ((located y).trans (flat.map_coordinates d_chart.1))
  calc
    dist (charts.develop c.val) (charts.develop d.val) =
        dist (charts.develop (inclusion x).val) (charts.develop (inclusion y).val) := by rw [at_c, at_d]
    _ = dist (x : Plane) (y : Plane) := rigid.dist_eq x y
    _ = P.surfaceDist c.val d.val := flat.coordinates_distance c_chart.1 d_chart.1

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
