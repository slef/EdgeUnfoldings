import SixVertexUnfolding.Geometry.JunctionEdgeTransitions

/-! A pair of actual radial triangles with one chosen planar placement.
Compatibility always concerns the complete maps of their surface points. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace RadialStripTriangle

/-- Reverse an agreement without changing its actual surface correspondence. -/
theorem AgreesAfter.symm {P : ConvexPolyhedron}
    {routes other : C(unitInterval, P.BoundaryCurve)} {p l r q u v : Plane}
    {D : RadialStripTriangle routes p l r} {E : RadialStripTriangle other q u v}
    {motion : Plane ≃ᵃⁱ[ℝ] Plane} (agrees : D.AgreesAfter E motion) :
    E.AgreesAfter D motion.symm := by
  refine ⟨agrees.1.symm, ?_⟩
  intro x hx hy
  rw [← agrees.2 x hy hx, motion.symm_apply_apply]

end RadialStripTriangle

/-- Both sides of a cut edge share this one local coordinate change. -/
structure PlacedCutEdgeTriangles {P : ConvexPolyhedron} {a : frontier P.body}
    (T : P.CutLocusTree a) {u v : T.vertices} (edge : T.graph.Adj u v)
    extends CutEdgeTriangles T edge where
  motion : Plane ≃ᵃⁱ[ℝ] Plane

namespace PlacedCutEdgeTriangles

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v w z : T.vertices} {edge : T.graph.Adj u v} {other : T.graph.Adj w z}

/-- Put the existing local placement into a selected global frame. -/
noncomputable def inFrame (D : PlacedCutEdgeTriangles T edge) (frame : Plane ≃ᵃⁱ[ℝ] Plane) :
    PlacedCutEdgeTriangles T edge :=
  ⟨D.toCutEdgeTriangles, D.motion.trans frame⟩

/-- The whole paired development agrees, allowing a consistent exchange of its two labels. -/
def AgreesAfter (D : PlacedCutEdgeTriangles T edge) (E : PlacedCutEdgeTriangles T other)
    (transition : Plane ≃ᵃⁱ[ℝ] Plane) : Prop :=
  (((D.first_triangle.move D.motion).AgreesAfter (E.first_triangle.move E.motion) transition ∧
    (D.second_triangle.move D.motion).AgreesAfter (E.second_triangle.move E.motion) transition) ∨
   ((D.first_triangle.move D.motion).AgreesAfter (E.second_triangle.move E.motion) transition ∧
    (D.second_triangle.move D.motion).AgreesAfter (E.first_triangle.move E.motion) transition))

/-- Reversing an edge swaps its base endpoints and preserves both full triangle maps. -/
def Reverses (D : PlacedCutEdgeTriangles T edge) (E : PlacedCutEdgeTriangles T other)
    (transition : Plane ≃ᵃⁱ[ℝ] Plane) : Prop :=
  transition (D.motion D.model.left) = E.motion E.model.right ∧
  transition (D.motion D.model.right) = E.motion E.model.left ∧
  D.AgreesAfter E transition

theorem AgreesAfter.symm {D : PlacedCutEdgeTriangles T edge} {E : PlacedCutEdgeTriangles T other}
    {transition : Plane ≃ᵃⁱ[ℝ] Plane} (agrees : D.AgreesAfter E transition) :
    E.AgreesAfter D transition.symm := by
  rcases agrees with same | swapped
  · exact Or.inl ⟨same.1.symm, same.2.symm⟩
  · exact Or.inr ⟨swapped.2.symm, swapped.1.symm⟩

theorem Reverses.symm {D : PlacedCutEdgeTriangles T edge} {E : PlacedCutEdgeTriangles T other}
    {transition : Plane ≃ᵃⁱ[ℝ] Plane} (reverses : D.Reverses E transition) :
    E.Reverses D transition.symm := by
  refine ⟨?_, ?_, reverses.2.2.symm⟩
  · rw [← reverses.2.1, transition.symm_apply_apply]
  · rw [← reverses.1, transition.symm_apply_apply]

/-- Full triangle agreement persists in any compatible pair of global frames. -/
theorem AgreesAfter.in_common_frame {D : PlacedCutEdgeTriangles T edge}
    {E : PlacedCutEdgeTriangles T other} {transition : Plane ≃ᵃⁱ[ℝ] Plane}
    (agrees : D.AgreesAfter E transition) (first second : Plane ≃ᵃⁱ[ℝ] Plane)
    (compatible : ∀ x, second (transition x) = first x) :
    (D.inFrame first).AgreesAfter (E.inFrame second) (AffineIsometryEquiv.refl ℝ Plane) := by
  rcases agrees with same | swapped
  · exact Or.inl ⟨same.1.in_common_frame first second compatible,
      same.2.in_common_frame first second compatible⟩
  · exact Or.inr ⟨swapped.1.in_common_frame first second compatible,
      swapped.2.in_common_frame first second compatible⟩

theorem Reverses.in_common_frame {D : PlacedCutEdgeTriangles T edge}
    {E : PlacedCutEdgeTriangles T other} {transition : Plane ≃ᵃⁱ[ℝ] Plane}
    (reverses : D.Reverses E transition) (first second : Plane ≃ᵃⁱ[ℝ] Plane)
    (compatible : ∀ x, second (transition x) = first x) :
    (D.inFrame first).Reverses (E.inFrame second) (AffineIsometryEquiv.refl ℝ Plane) := by
  refine ⟨?_, ?_, reverses.2.2.in_common_frame first second compatible⟩
  · change first (D.motion D.model.left) = second (E.motion E.model.right)
    rw [← compatible, reverses.1]
  · change first (D.motion D.model.right) = second (E.motion E.model.left)
    rw [← compatible, reverses.2.1]

/-- The genuine reverse development provides both base positions and full surface agreement. -/
theorem exists_reversal (D : PlacedCutEdgeTriangles T edge)
    (E : PlacedCutEdgeTriangles T edge.symm) : ∃ transition, D.Reverses E transition := by
  obtain ⟨motion, left, right, cases⟩ := D.toCutEdgeTriangles.reversal_agreement E.toCutEdgeTriangles
  refine ⟨D.motion.symm.trans (motion.trans E.motion), ?_, ?_, ?_⟩
  · change E.motion (motion (D.motion.symm (D.motion D.model.left))) = E.motion E.model.right
    rw [D.motion.symm_apply_apply, left]
  · change E.motion (motion (D.motion.symm (D.motion D.model.right))) = E.motion E.model.left
    rw [D.motion.symm_apply_apply, right]
  · rcases cases with same | swapped
    · exact Or.inl ⟨same.2.2.2.2.1.move D.motion E.motion, same.2.2.2.2.2.move D.motion E.motion⟩
    · exact Or.inr ⟨swapped.2.2.2.2.1.move D.motion E.motion, swapped.2.2.2.2.2.move D.motion E.motion⟩

/-- Opposite orientations of an actual cut edge admit such a complete agreement. -/
theorem exists_reversal_agreement (D : PlacedCutEdgeTriangles T edge)
    (E : PlacedCutEdgeTriangles T edge.symm) : ∃ transition, D.AgreesAfter E transition := by
  obtain ⟨transition, reverses⟩ := D.exists_reversal E
  exact ⟨transition, reverses.2.2⟩

end PlacedCutEdgeTriangles

/-- Forget only the angular chart labels, retaining the actual triangles and their placement. -/
def IncidentTriangles.placed {P : ConvexPolyhedron} {a : frontier P.body}
    {T : P.CutLocusTree a} {u v : T.vertices} {edge : T.graph.Adj u v}
    {chart : P.CutVoronoiChart a (T.vertexTarget u)} {angle : ℝ}
    (D : IncidentTriangles T edge chart angle) : PlacedCutEdgeTriangles T edge :=
  ⟨D.toCutEdgeTriangles, D.motion⟩

end SixVertexUnfolding.ConvexPolyhedron
