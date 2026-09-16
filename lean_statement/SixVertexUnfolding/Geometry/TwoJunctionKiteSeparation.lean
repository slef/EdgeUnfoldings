import SixVertexUnfolding.Geometry.JunctionEdgeIndices
import SixVertexUnfolding.Geometry.ExpandingRegionChains
import SixVertexUnfolding.Geometry.JunctionTerminalStep

/-! Separate two kites at different junctions across their shared middle
edge. The returned move retains agreement of both complete middle triangles. -/

namespace SixVertexUnfolding.ConvexPolyhedron.JunctionFan

open Real Set Wedge

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u : T.vertices} (fan : JunctionFan T u)

/-- The first and last kites of a three-edge chain are separate in the
same chart, using the actual triangle-preserving transition across the middle edge. -/
theorem two_junction_kites_nonoverlap
    (incoming middle : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (first_distinct : incoming ≠ middle)
    (next : JunctionFan T (fan.order.neighbors middle).val)
    (outgoing : circularGapMidpoints next.order.angles next.order.first next.order.last)
    (last_distinct : next.edgeIndex (fan.order.neighbors middle).property.symm ≠ outgoing)
    (budget : (fan.triangles incoming).model.sourceAngle + (fan.triangles middle).model.sourceAngle +
      (next.triangles outgoing).model.sourceAngle ≤ π) :
    ∃ move : fan.WedgeMove incoming middle
        (next.edgeTriangles (fan.order.neighbors middle).property.symm)
        (π / 2 + (fan.triangles incoming).model.sourceAngle),
      Disjoint (move.motion '' (fan.triangles incoming).developedKite)
        (interior (next.triangles outgoing).developedKite) := by
  have first_positive := (fan.triangles incoming).model.sourceAngle_pos
  have last_positive := (next.triangles outgoing).model.sourceAngle_pos
  obtain ⟨move⟩ := fan.exists_wedge_move incoming middle first_distinct
    (next.edgeTriangles (fan.order.neighbors middle).property.symm)
    (π / 2 + (fan.triangles incoming).model.sourceAngle) (by linarith) (by linarith)
  have contained : move.motion '' (fan.triangles incoming).developedKite ⊆
      (next.edgeTriangles (fan.order.neighbors middle).property.symm).incomingWedge
        (π / 2 + (fan.triangles incoming).model.sourceAngle +
          (fan.triangles middle).model.sourceAngle) :=
    (image_mono (fan.triangles incoming).initial_kite_in_wedge).trans move.toRegionStep.carries_before
  rw [next.edgeTriangles_wedge] at contained
  have avoids := next.incoming_wedge_avoids_kite
    (next.edgeIndex (fan.order.neighbors middle).property.symm) outgoing last_distinct
    (π / 2 + (fan.triangles incoming).model.sourceAngle + (fan.triangles middle).model.sourceAngle)
    (by linarith [(fan.triangles middle).model.sourceAngle_pos]) (by linarith)
  exact ⟨move, avoids.mono contained Subset.rfl⟩

end SixVertexUnfolding.ConvexPolyhedron.JunctionFan
