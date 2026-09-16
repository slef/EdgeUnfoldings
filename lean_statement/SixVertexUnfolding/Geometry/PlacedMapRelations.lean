import SixVertexUnfolding.Geometry.PlacedTriangleSides

/-! Complete triangle-map agreement preserves placements of actual
surface points. A change of frame carries both coordinates and labels. -/

namespace SixVertexUnfolding.ConvexPolyhedron.PlacedCutEdgeTriangles

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v w z : T.vertices} {edge : T.graph.Adj u v} {other : T.graph.Adj w z}
    {D : PlacedCutEdgeTriangles T edge} {E : PlacedCutEdgeTriangles T other}

/-- Transport each entire labelled triangle, respecting the possible exchange of sides. -/
theorem AgreesAfter.places {motion : Plane ≃ᵃⁱ[ℝ] Plane} (agrees : D.AgreesAfter E motion)
    {b : frontier P.body} {x : Plane} (placed : D.Places b x) : E.Places b (motion x) := by
  obtain ⟨side, inside, at_point⟩ := placed
  rcases agrees with same | swapped
  · cases side
    · refine ⟨false, same.1.1 ▸ inside, ?_⟩
      exact (same.1.2 b inside _).symm.trans (congrArg motion at_point)
    · refine ⟨true, same.2.1 ▸ inside, ?_⟩
      exact (same.2.2 b inside _).symm.trans (congrArg motion at_point)
  · cases side
    · refine ⟨true, swapped.1.1 ▸ inside, ?_⟩
      exact (swapped.1.2 b inside _).symm.trans (congrArg motion at_point)
    · refine ⟨false, swapped.2.1 ▸ inside, ?_⟩
      exact (swapped.2.2 b inside _).symm.trans (congrArg motion at_point)

theorem places_inFrame (D : PlacedCutEdgeTriangles T edge) (frame : Plane ≃ᵃⁱ[ℝ] Plane)
    (b : frontier P.body) (x : Plane) :
    (D.inFrame frame).Places b x ↔ D.Places b (frame.symm x) := by
  constructor
  · rintro ⟨side, inside, at_point⟩
    refine ⟨side, inside, ?_⟩
    change frame (D.motion ((D.triangle side).homeomorph ⟨b, inside⟩)) = x at at_point
    change D.motion ((D.triangle side).homeomorph ⟨b, inside⟩) = frame.symm x
    rw [← at_point, frame.symm_apply_apply]
  · rintro ⟨side, inside, at_point⟩
    refine ⟨side, inside, ?_⟩
    change frame (D.motion ((D.triangle side).homeomorph ⟨b, inside⟩)) = x
    change D.motion ((D.triangle side).homeomorph ⟨b, inside⟩) = frame.symm x at at_point
    rw [at_point, frame.apply_symm_apply]

theorem placesOnRay_inFrame (D : PlacedCutEdgeTriangles T edge) (frame : Plane ≃ᵃⁱ[ℝ] Plane)
    (s : unitInterval) (b : frontier P.body) (x : Plane) :
    (D.inFrame frame).PlacesOnRay s b x ↔ D.PlacesOnRay s b (frame.symm x) := by
  have mapped (side : Bool) (t : unitInterval) :
      triangleFanMap (frame (D.motion (D.apex side))) (frame (D.motion D.model.left))
        (frame (D.motion D.model.right)) (s, t) =
      frame (triangleFanMap (D.motion (D.apex side)) (D.motion D.model.left)
        (D.motion D.model.right) (s, t)) := by
    change _ = frame.toAffineEquiv (AffineMap.lineMap _ (AffineMap.lineMap _ _ (s : ℝ)) (t : ℝ))
    rw [AffineEquiv.apply_lineMap, AffineEquiv.apply_lineMap]
    rfl
  constructor
  · rintro ⟨side, t, at_point, placed⟩
    refine ⟨side, t, at_point, ?_⟩
    change triangleFanMap (frame (D.motion (D.apex side))) (frame (D.motion D.model.left))
      (frame (D.motion D.model.right)) (s, t) = x at placed
    rw [mapped] at placed
    rw [← placed, frame.symm_apply_apply]
  · rintro ⟨side, t, at_point, placed⟩
    refine ⟨side, t, at_point, ?_⟩
    change triangleFanMap (frame (D.motion (D.apex side))) (frame (D.motion D.model.left))
      (frame (D.motion D.model.right)) (s, t) = x
    rw [mapped, placed, frame.apply_symm_apply]

end SixVertexUnfolding.ConvexPolyhedron.PlacedCutEdgeTriangles
