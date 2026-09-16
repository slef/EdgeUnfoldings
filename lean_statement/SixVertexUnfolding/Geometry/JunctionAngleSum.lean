import SixVertexUnfolding.Geometry.JunctionOrder
import SixVertexUnfolding.Geometry.JunctionGapAngles
import SixVertexUnfolding.Geometry.CircularGapSum

/-! The actual metric triangles around a flat cut-tree junction have
total corner angle exactly 2π. Each incident edge is counted once.
The assertion is independent of the chosen metric models. -/

namespace SixVertexUnfolding.ConvexPolyhedron.JunctionOrder

open Real Set EuclideanGeometry
open scoped BigOperators

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
  {u : T.vertices} (order : JunctionOrder T u)

include order in
/-- All incident triangle corners fill one full turn at a nonvertex junction. -/
theorem sum_junction_angles [Fintype {v : T.vertices // T.graph.Adj u v}]
    (models : ∀ v : {v : T.vertices // T.graph.Adj u v}, CutEdgeMetricModel T v.property) :
    ∑ v, (angle (models v).first (models v).left (models v).right +
      angle (models v).second (models v).left (models v).right) = 2 * π := by
  let gaps := circularGapMidpointEquiv order.angles order.increasing order.bounds
    order.first order.last order.at_last
  let edges := gaps.trans order.neighbors
  have corners (i : Fin order.chart.sources.ncard) :
      angle (models (edges i)).first (models (edges i)).left (models (edges i)).right +
        angle (models (edges i)).second (models (edges i)).left (models (edges i)).right =
          circularGapEnd order.angles order.first i - order.angles i := by
    have gap := circularGapEnd_gap order.angles order.first order.last i order.at_last
    obtain ⟨ordered, width, _, _, first_source, second_source, empty_gap⟩ := circular_gap_spec
      order.sites order.angles order.increasing order.bounds order.chart.origin
      (P.surfaceDist a (T.vertexTarget u)) order.position order.first order.last
      order.at_first order.at_last order.two gap
    have on_ray (ρ : ℝ) (hr : ρ ∈ Ioo (0 : ℝ) order.radius) :
        order.chart.map (order.chart.origin + ρ •
          direction ((order.angles i + circularGapEnd order.angles order.first i) / 2)) ∈
            openSegment ℝ (T.vertexTarget u : Space) ((edges i).val : Space) :=
      order.rays (gaps i) ρ hr
    obtain ⟨first_angle, second_angle⟩ := order.chart.incident_gap_junction_angles T (edges i).property
      rfl (models (edges i)) ordered width first_source second_source empty_gap order.radius_positive on_ray
    linarith
  calc
    _ = ∑ i, (angle (models (edges i)).first (models (edges i)).left (models (edges i)).right +
        angle (models (edges i)).second (models (edges i)).left (models (edges i)).right) :=
      (Equiv.sum_comp edges _).symm
    _ = ∑ i, (circularGapEnd order.angles order.first i - order.angles i) :=
      Finset.sum_congr rfl (fun i _ => corners i)
    _ = 2 * π := sum_circularGap_widths order.angles order.first order.at_first

end SixVertexUnfolding.ConvexPolyhedron.JunctionOrder

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Real Set EuclideanGeometry
open scoped BigOperators

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- No chart or angular ordering needs to be supplied: the actual
nonvertex cut junction itself supplies the full-turn angle identity. -/
theorem sum_nonvertex_junction_angles (a : frontier P.body) (T : P.CutLocusTree a)
    (u : T.vertices) (not_vertex : (u : Space) ∉ P.vertices)
    [Fintype {v : T.vertices // T.graph.Adj u v}]
    (models : ∀ v : {v : T.vertices // T.graph.Adj u v}, CutEdgeMetricModel T v.property) :
    ∑ v, (angle (models v).first (models v).left (models v).right +
      angle (models v).second (models v).left (models v).right) = 2 * π := by
  obtain ⟨order⟩ := graph.exists_junction_order small_faces a T u not_vertex
  exact order.sum_junction_angles models

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
