import SixVertexUnfolding.Geometry.JunctionOrder
import SixVertexUnfolding.Geometry.JunctionTriangleLabels
import SixVertexUnfolding.Geometry.CutEdgeTriangles

/-! All incident radial triangles at a nonvertex junction are chosen at
once, in one common coordinate frame and with their actual route labels.
This is geometric assembly data, not yet a quotient cut surface.
-/

namespace SixVertexUnfolding.ConvexPolyhedron

open Real Set

/-- The two actual radial developments of one incident edge, placed and labelled. -/
structure IncidentTriangles {P : ConvexPolyhedron} {a : frontier P.body}
    (T : P.CutLocusTree a) {u v : T.vertices} (edge : T.graph.Adj u v)
    (chart : P.CutVoronoiChart a (T.vertexTarget u)) (angle : ℝ) extends CutEdgeTriangles T edge where
  motion : Plane ≃ᵃⁱ[ℝ] Plane
  at_junction : motion model.left = chart.origin
  at_neighbor : motion model.right = chart.origin + dist (u : Space) (v : Space) • direction angle
  first_label : chart.Represents (motion model.first) (first 0)
  second_label : chart.Represents (motion model.second) (second 0)

/-- A finite junction fan retains all actual strips and their common-chart placements. -/
structure JunctionFan {P : ConvexPolyhedron} {a : frontier P.body}
    (T : P.CutLocusTree a) (u : T.vertices) where
  order : JunctionOrder T u
  triangles : ∀ m : circularGapMidpoints order.angles order.first order.last,
    IncidentTriangles T (order.neighbors m).property order.chart m

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Simultaneous incident-edge developments with one circular order and
one chart. Every triangle retains its original surface parametrization. -/
theorem exists_junction_fan (a : frontier P.body) (T : P.CutLocusTree a)
    (u : T.vertices) (not_vertex : (u : Space) ∉ P.vertices) : Nonempty (JunctionFan T u) := by
  classical
  obtain ⟨order⟩ := graph.exists_junction_order small_faces a T u not_vertex
  have developments (m : circularGapMidpoints order.angles order.first order.last) :
      Nonempty (IncidentTriangles T (order.neighbors m).property order.chart m) := by
    let v := (order.neighbors m).val
    let edge : T.graph.Adj u v := (order.neighbors m).property
    obtain ⟨S⟩ := graph.exists_cut_edge_strips small_faces a T edge
    obtain ⟨M, first, second, agrees, member, ⟨D⟩, ⟨E⟩⟩ :=
      graph.exists_cut_edge_triangle_developments small_faces a T edge S
    obtain ⟨α, β, ordered, one_turn, midpoint, _, _, first_source, second_source, empty_gap⟩ :=
      circular_midpoint_gap order.sites order.angles order.increasing order.bounds order.chart.origin
        (P.surfaceDist a (T.vertexTarget u)) order.position order.first order.last
        order.at_first order.at_last order.two m.property
    have on_ray (ρ : ℝ) (hr : ρ ∈ Ioo (0 : ℝ) order.radius) :
        order.chart.map (order.chart.origin + ρ • direction ((α + β) / 2)) ∈
          openSegment ℝ (T.vertexTarget u : Space) (v : Space) := by
      rw [← midpoint]
      exact order.rays m ρ hr
    obtain ⟨motion, at_junction, at_neighbor, first_label, second_label⟩ :=
      order.chart.incident_placement_with_routes graph small_faces T edge rfl not_vertex
        M S first second agrees member ordered one_turn first_source second_source empty_gap
        order.radius_positive on_ray
    refine ⟨⟨⟨S, M, first, second, agrees, member, D, E⟩, motion, at_junction, ?_,
      first_label, second_label⟩⟩
    simpa only [← midpoint] using at_neighbor
  exact ⟨⟨order, fun m => Classical.choice (developments m)⟩⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
