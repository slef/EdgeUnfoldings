import SixVertexUnfolding.Geometry.EdgeCircleMap
import SixVertexUnfolding.Geometry.CircleRealLifts

/-! A contractible graph trace supplies a real potential increasing by one
on one selected edge and constant on every other edge. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} (K : P.EmbeddedCutGraph a)

/-- Lift the one-edge circle map and read its values at the graph vertices. -/
theorem exists_edge_potential [ContractibleSpace (P.cutSetInSpace a)]
    (u v : K.vertices) (edge : K.graph.Adj u v) :
    ∃ height : K.vertices → ℝ, height v = height u + 1 ∧
      ∀ p q, K.graph.Adj p q → s(p, q) ≠ s(u, v) → height p = height q := by
  let circle : C(P.cutSetInSpace a, AddCircle (1 : ℝ)) :=
    ⟨fun x => K.edgeCircleMap u v x, (K.edgeCircleMap_continuous u v edge).restrict⟩
  obtain ⟨lift, projects⟩ := circle_map_real_lift circle
  let height : K.vertices → ℝ := fun p => lift ⟨p, K.vertex_in_trace p⟩
  refine ⟨height, ?_, ?_⟩
  · have turn : ∀ t : unitInterval, ((lift.comp (K.edgePath edge)) t : AddCircle (1 : ℝ)) =
        ((t : ℝ) : AddCircle (1 : ℝ)) := by
      intro t
      rw [ContinuousMap.comp_apply, projects]
      change K.edgeCircleMap u v (AffineMap.lineMap (u : Space) (v : Space) (t : ℝ)) = _
      rw [K.edgeCircleMap_on_selected u v edge, segmentCoordinate_lineMap u v
        (fun same => edge.ne (Subtype.ext same))]
      rw [segment_eq_image_lineMap]
      exact ⟨t, t.property, rfl⟩
    have increment := real_lift_one_turn (lift.comp (K.edgePath edge)) turn
    simpa only [ContinuousMap.comp_apply, K.edgePath_zero, K.edgePath_one] using increment
  · intro p q other different
    have constant : ∀ t : unitInterval, ((lift.comp (K.edgePath other)) t : AddCircle (1 : ℝ)) = 0 := by
      intro t
      rw [ContinuousMap.comp_apply, projects]
      apply K.edgeCircleMap_on_other u v edge other
        (fun same => different (Sym2.eq_iff.mpr same).symm)
      change AffineMap.lineMap (p : Space) (q : Space) (t : ℝ) ∈ segment ℝ (p : Space) (q : Space)
      rw [segment_eq_image_lineMap]
      exact ⟨t, t.property, rfl⟩
    have equal := real_lift_constant_circle (lift.comp (K.edgePath other)) constant
    simpa only [ContinuousMap.comp_apply, K.edgePath_zero, K.edgePath_one] using equal

end SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph
