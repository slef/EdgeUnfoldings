import SixVertexUnfolding.Geometry.TwoJunctionKiteSeparation
import SixVertexUnfolding.Geometry.CutTreePathBudget

/-! The actual source cone supplies the three-angle budget for separation
across two junctions; no numerical angle premise is left to the caller. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Real Set Wedge

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    {a : frontier P.body} (T : P.CutLocusTree a)

include small_faces in
theorem two_junction_source_budget (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space))
    {u : T.vertices} (fan : JunctionFan T u)
    (incoming middle : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (first_distinct : incoming ≠ middle)
    (next : JunctionFan T (fan.order.neighbors middle).val)
    (outgoing : circularGapMidpoints next.order.angles next.order.first next.order.last)
    (last_distinct : next.edgeIndex (fan.order.neighbors middle).property.symm ≠ outgoing) :
    (fan.triangles incoming).model.sourceAngle + (fan.triangles middle).model.sourceAngle +
      (next.triangles outgoing).model.sourceAngle < π := by
  classical
  letI : Fintype T.vertices := T.finite_vertices.fintype
  let models (d : T.graph.Dart) : CutEdgeMetricModel T d.adj :=
    Classical.choice (graph.exists_cut_edge_metric_model small_faces a T d.adj)
  let p := (fan.order.neighbors incoming).val
  let v := (fan.order.neighbors middle).val
  let q := (next.order.neighbors outgoing).val
  have uv : u ≠ v := (fan.order.neighbors middle).property.ne
  have up : u ≠ p := (fan.order.neighbors incoming).property.ne
  have vq : v ≠ q := (next.order.neighbors outgoing).property.ne
  have pv : p ≠ v := by
    intro same
    exact first_distinct (fan.order.neighbors.injective (Subtype.ext same))
  have qu : q ≠ u := by
    intro same
    apply last_distinct
    apply next.order.neighbors.injective
    rw [next.edgeIndex_neighbor]
    exact Subtype.ext same.symm
  let first : T.graph.Dart := ⟨(u, p), (fan.order.neighbors incoming).property⟩
  let second : T.graph.Dart := ⟨(u, v), (fan.order.neighbors middle).property⟩
  let third : T.graph.Dart := ⟨(v, q), (next.order.neighbors outgoing).property⟩
  have different12 : first ≠ second := fun same => pv (congrArg (fun d : T.graph.Dart => d.snd) same)
  have different13 : first ≠ third := fun same => uv (congrArg (fun d : T.graph.Dart => d.fst) same)
  have different23 : second ≠ third := fun same => uv (congrArg (fun d : T.graph.Dart => d.fst) same)
  have no_reverse (d : T.graph.Dart) (member : d ∈ ({first, second, third} : Finset T.graph.Dart)) :
      d.symm ∉ ({first, second, third} : Finset T.graph.Dart) := by
    intro reversed
    simp only [Finset.mem_insert, Finset.mem_singleton] at member reversed
    rcases member with rfl | rfl | rfl <;> rcases reversed with same | same | same
    all_goals
      have fronts := congrArg (fun d : T.graph.Dart => d.fst) same
      have backs := congrArg (fun d : T.graph.Dart => d.snd) same
      dsimp [first, second, third] at fronts backs
      first
      | exact uv fronts
      | exact uv fronts.symm
      | exact up fronts
      | exact up fronts.symm
      | exact pv fronts
      | exact pv fronts.symm
      | exact qu fronts
      | exact qu fronts.symm
      | exact vq fronts
      | exact vq fronts.symm
      | exact pv backs
      | exact pv backs.symm
      | exact qu backs
      | exact qu backs.symm
  have bounded := (T.selected_source_angle_sum_le_half models {first, second, third} no_reverse).trans_lt
    (graph.half_source_angle_sum_lt_pi small_faces T models source at_source)
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto),
    Finset.sum_insert (by simpa only [Finset.mem_singleton] using different23), Finset.sum_singleton] at bounded
  rw [(models first).same_edge_sourceAngle (fan.triangles incoming).model,
    (models second).same_edge_sourceAngle (fan.triangles middle).model,
    (models third).same_edge_sourceAngle (next.triangles outgoing).model] at bounded
  linarith

include small_faces in
/-- Whole kites at different actual junctions are separated by the
triangle-preserving middle-edge transition, with its budget already proved. -/
theorem two_junction_kites_nonoverlap (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space))
    {u : T.vertices} (fan : JunctionFan T u)
    (incoming middle : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (first_distinct : incoming ≠ middle)
    (next : JunctionFan T (fan.order.neighbors middle).val)
    (outgoing : circularGapMidpoints next.order.angles next.order.first next.order.last)
    (last_distinct : next.edgeIndex (fan.order.neighbors middle).property.symm ≠ outgoing) :
    ∃ move : fan.WedgeMove incoming middle
        (next.edgeTriangles (fan.order.neighbors middle).property.symm)
        (π / 2 + (fan.triangles incoming).model.sourceAngle),
      Disjoint (move.motion '' (fan.triangles incoming).developedKite)
        (interior (next.triangles outgoing).developedKite) :=
  fan.two_junction_kites_nonoverlap incoming middle first_distinct next outgoing last_distinct
    (graph.two_junction_source_budget small_faces T source at_source fan incoming middle
      first_distinct next outgoing last_distinct).le

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
