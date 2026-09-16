import SixVertexUnfolding.Geometry.ClosedCutEdgeRoutes
import SixVertexUnfolding.Geometry.ClosedRouteStrips

/-! A closed strip collapses exactly its source edge. Every other
surface point retains a unique target parameter and a unique route time. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutLocusTree

variable {P : ConvexPolyhedron} {a : frontier P.body} (T : P.CutLocusTree a)

theorem closedEdgeTarget_injective {u v : T.vertices} (edge : T.graph.Adj u v) :
    Function.Injective (T.closedEdgeTarget edge) := by
  intro s t same
  apply Subtype.ext
  exact AffineMap.lineMap_injective ℝ (fun equal => edge.ne (Subtype.ext equal))
    (congrArg (fun b : frontier P.body => (b : Space)) same)

end CutLocusTree

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The only identifications in a closed route strip occur at time zero, the common source. -/
theorem closed_strip_fibers (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v)
    (routes : C(unitInterval, P.BoundaryCurve))
    (member : ∀ x, routes x ∈ P.geodesicFiber a (T.closedEdgeTarget edge x))
    (p q : unitInterval × unitInterval) :
    closedRouteStripMap routes p = closedRouteStripMap routes q ↔
      (p.2 = 0 ∧ q.2 = 0) ∨ p = q := by
  have first (x : unitInterval) : routes x 0 = a := congrArg Prod.fst (member x).2
  have different (x : unitInterval) : a ≠ T.closedEdgeTarget edge x := by
    intro same
    have cut := T.closedEdgeTarget_cut edge x
    rw [← same] at cut
    exact P.source_not_cutSet a cut
  have injective (x : unitInterval) : Function.Injective (routes x) :=
    P.geodesicFiber_injective a _ (different x) (routes x) (member x)
  constructor
  · intro meet
    change routes p.1 p.2 = routes q.1 q.2 at meet
    by_cases zero : p.2 = 0
    · left
      refine ⟨zero, injective q.1 ?_⟩
      rw [zero, first p.1] at meet
      exact meet.symm.trans (first q.1).symm
    · have positive : 0 < p.2 := lt_of_le_of_ne p.2.property.1 (Ne.symm zero)
      have qzero : q.2 ≠ 0 := by
        intro at_zero
        rw [at_zero, first q.1] at meet
        exact zero (injective p.1 (meet.trans (first p.1).symm))
      have qpositive : 0 < q.2 := lt_of_le_of_ne q.2.property.1 (Ne.symm qzero)
      obtain ⟨p_nonzero, p_end⟩ := graph.cutEndpoint_on_route small_faces a _ (T.closedEdgeTarget_cut edge p.1)
        (routes p.1) (member p.1) p.2 positive
      obtain ⟨q_nonzero, q_end⟩ := graph.cutEndpoint_on_route small_faces a _ (T.closedEdgeTarget_cut edge q.1)
        (routes q.1) (member q.1) q.2 qpositive
      have same_input : (⟨routes p.1 p.2, p_nonzero⟩ : {b : frontier P.body // b ≠ a}) =
          ⟨routes q.1 q.2, q_nonzero⟩ := Subtype.ext meet
      rw [same_input] at p_end
      have targets := T.closedEdgeTarget_injective edge (p_end.symm.trans q_end)
      right
      apply Prod.ext targets
      rw [targets] at meet
      exact injective q.1 meet
  · rintro (⟨hp, hq⟩ | rfl)
    · change routes p.1 p.2 = routes q.1 q.2
      rw [hp, hq, first, first]
    · rfl

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
