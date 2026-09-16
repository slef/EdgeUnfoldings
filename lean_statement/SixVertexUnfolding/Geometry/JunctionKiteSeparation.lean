import SixVertexUnfolding.Geometry.JunctionTerminalStep
import SixVertexUnfolding.Geometry.CutTreePathBudget

/-! Any two complete kites incident at one flat junction have disjoint
interiors. The actual source cone supplies their two-angle budget. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Real Set Wedge

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    {a : frontier P.body} (T : P.CutLocusTree a)

include small_faces in
/-- Distinct incident kites use two different unoriented tree edges,
so their source angles fit strictly inside the source's half-cone budget. -/
theorem junction_source_pair_budget (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space))
    {u : T.vertices} (fan : JunctionFan T u)
    (incoming outgoing : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (distinct : incoming ≠ outgoing) :
    (fan.triangles incoming).model.sourceAngle + (fan.triangles outgoing).model.sourceAngle < π := by
  classical
  letI : Fintype T.vertices := T.finite_vertices.fintype
  let models (d : T.graph.Dart) : CutEdgeMetricModel T d.adj :=
    Classical.choice (graph.exists_cut_edge_metric_model small_faces a T d.adj)
  let first : T.graph.Dart := ⟨(u, (fan.order.neighbors incoming).val), (fan.order.neighbors incoming).property⟩
  let second : T.graph.Dart := ⟨(u, (fan.order.neighbors outgoing).val), (fan.order.neighbors outgoing).property⟩
  have different : first ≠ second := by
    intro same
    have neighbors : (fan.order.neighbors incoming).val = (fan.order.neighbors outgoing).val :=
      congrArg (fun d : T.graph.Dart => d.snd) same
    exact distinct (fan.order.neighbors.injective (Subtype.ext neighbors))
  have starts (d : T.graph.Dart) (member : d ∈ ({first, second} : Finset T.graph.Dart)) : d.fst = u := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl <;> rfl
  have no_reverse (d : T.graph.Dart) (member : d ∈ ({first, second} : Finset T.graph.Dart)) :
      d.symm ∉ ({first, second} : Finset T.graph.Dart) := by
    intro reverse
    have forward := starts d member
    have backwards : d.snd = u := starts d.symm reverse
    exact d.adj.ne (forward.trans backwards.symm)
  have bounded := (T.selected_source_angle_sum_le_half models {first, second} no_reverse).trans_lt
    (graph.half_source_angle_sum_lt_pi small_faces T models source at_source)
  rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using different), Finset.sum_singleton] at bounded
  have first_angle := (models first).same_edge_sourceAngle (fan.triangles incoming).model
  have second_angle := (models second).same_edge_sourceAngle (fan.triangles outgoing).model
  rwa [first_angle, second_angle] at bounded

include small_faces in
/-- The whole first kite misses the interior of the second in their already
chosen common chart. No numerical budget or new placement is assumed. -/
theorem junction_kites_nonoverlap (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space))
    {u : T.vertices} (fan : JunctionFan T u)
    (incoming outgoing : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (distinct : incoming ≠ outgoing) :
    Disjoint (fan.triangles incoming).developedKite
      (interior (fan.triangles outgoing).developedKite) :=
  fan.incident_kites_nonoverlap incoming outgoing distinct
    (graph.junction_source_pair_budget small_faces T source at_source fan incoming outgoing distinct).le

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
