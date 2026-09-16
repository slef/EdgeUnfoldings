import SixVertexUnfolding.Geometry.CutEdgeReversalAgreement
import SixVertexUnfolding.Geometry.JunctionFan

/-! Independently constructed junction charts fit across their common
edge by one transition motion preserving the complete triangle maps. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace RadialStripTriangle

variable {P : ConvexPolyhedron} {routes other : C(unitInterval, P.BoundaryCurve)}
    {p l r q L R : Plane} {D : RadialStripTriangle routes p l r}
    {E : RadialStripTriangle other q L R} {motion : Plane ≃ᵃⁱ[ℝ] Plane}

/-- Change both coordinate frames while retaining the same surface agreement. -/
theorem AgreesAfter.move (agrees : D.AgreesAfter E motion)
    (first second : Plane ≃ᵃⁱ[ℝ] Plane) :
    (D.move first).AgreesAfter (E.move second) (first.symm.trans (motion.trans second)) := by
  refine ⟨agrees.1, ?_⟩
  intro x hx hy
  change second (motion (first.symm (first (D.homeomorph ⟨x, hx⟩)))) = second (E.homeomorph ⟨x, hy⟩)
  rw [first.symm_apply_apply, agrees.2 x hx hy]

/-- Coordinates propagated along a chain make the two full developments
agree directly in the resulting common plane. -/
theorem AgreesAfter.in_common_frame (agrees : D.AgreesAfter E motion)
    (first second : Plane ≃ᵃⁱ[ℝ] Plane)
    (compatible : ∀ x, second (motion x) = first x) :
    (D.move first).AgreesAfter (E.move second) (AffineIsometryEquiv.refl ℝ Plane) := by
  refine ⟨agrees.1, ?_⟩
  intro x hx hy
  change first (D.homeomorph ⟨x, hx⟩) = second (E.homeomorph ⟨x, hy⟩)
  rw [← compatible, agrees.2 x hx hy]

end RadialStripTriangle

namespace IncidentTriangles

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v}
    {first_chart : P.CutVoronoiChart a (T.vertexTarget u)}
    {second_chart : P.CutVoronoiChart a (T.vertexTarget v)} {θ φ : ℝ}
    (D : IncidentTriangles T edge first_chart θ)
    (E : IncidentTriangles T edge.symm second_chart φ)

/-- The two junction charts describe the same whole kite under one rigid transition.
The only alternatives are the two consistent source-label correspondences. -/
theorem exists_edge_transition :
    ∃ transition : Plane ≃ᵃⁱ[ℝ] Plane,
      transition first_chart.origin = second_chart.origin + dist (v : Space) (u : Space) • direction φ ∧
      transition (first_chart.origin + dist (u : Space) (v : Space) • direction θ) = second_chart.origin ∧
      (((D.first_triangle.move D.motion).AgreesAfter (E.first_triangle.move E.motion) transition ∧
        (D.second_triangle.move D.motion).AgreesAfter (E.second_triangle.move E.motion) transition ∧
        (∀ t, D.first t = E.first (unitInterval.symm t)) ∧
        (∀ t, D.second t = E.second (unitInterval.symm t))) ∨
       ((D.first_triangle.move D.motion).AgreesAfter (E.second_triangle.move E.motion) transition ∧
        (D.second_triangle.move D.motion).AgreesAfter (E.first_triangle.move E.motion) transition ∧
        (∀ t, D.first t = E.second (unitInterval.symm t)) ∧
        (∀ t, D.second t = E.first (unitInterval.symm t)))) := by
  obtain ⟨motion, left, right, cases⟩ := D.toCutEdgeTriangles.reversal_agreement E.toCutEdgeTriangles
  let transition := D.motion.symm.trans (motion.trans E.motion)
  have apply_transition (x : Plane) : transition x = E.motion (motion (D.motion.symm x)) := rfl
  refine ⟨transition, ?_, ?_, ?_⟩
  · rw [apply_transition, ← D.at_junction, D.motion.symm_apply_apply, left, E.at_neighbor]
  · rw [apply_transition, ← D.at_neighbor, D.motion.symm_apply_apply, right, E.at_junction]
  · rcases cases with same | swapped
    · exact Or.inl ⟨same.2.2.2.2.1.move D.motion E.motion,
        same.2.2.2.2.2.move D.motion E.motion, same.2.2.1, same.2.2.2.1⟩
    · exact Or.inr ⟨swapped.2.2.2.2.1.move D.motion E.motion,
        swapped.2.2.2.2.2.move D.motion E.motion, swapped.2.2.1, swapped.2.2.2.1⟩

end IncidentTriangles
end SixVertexUnfolding.ConvexPolyhedron
