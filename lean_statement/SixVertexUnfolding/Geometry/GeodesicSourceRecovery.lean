import SixVertexUnfolding.Geometry.GeodesicFibers
import SixVertexUnfolding.Geometry.TerminalSourceRecovery

/-! Source copies are recovered continuously from two curve evaluations.
Their finite set makes the recovered copy locally constant among actual routes. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set BoundedContinuousFunction

/-- Extend the final straight segment back to time zero in the fixed face coordinates. -/
noncomputable def recoveredSource (P : ConvexPolyhedron) (F : P.Face) (t : unitInterval)
    (f : P.BoundaryCurve) : Plane :=
  (1 - (t : ℝ))⁻¹ • (P.faceCoordinates F (f t) - (t : ℝ) • P.faceCoordinates F (f 1))

theorem recoveredSource_continuous (P : ConvexPolyhedron) (F : P.Face) (t : unitInterval) :
    Continuous (P.recoveredSource F t) := by
  have evaluation (u : unitInterval) : Continuous (fun f : P.BoundaryCurve => P.faceCoordinates F (f u)) :=
    (P.faceCoordinates F).continuous_of_finiteDimensional.comp
      (continuous_subtype_val.comp (continuous_eval_const u))
  exact continuous_const.smul ((evaluation t).sub (continuous_const.smul (evaluation 1)))

/-- The recovered copy is the only possible source in the affine terminal formula. -/
theorem recoveredSource_eq (P : ConvexPolyhedron) (F : P.Face) (t : unitInterval) (before : t < 1)
    (f : P.BoundaryCurve) (source : Plane)
    (formula : P.faceCoordinates F (f t) = AffineMap.lineMap source (P.faceCoordinates F (f 1)) (t : ℝ)) :
    P.recoveredSource F t f = source := by
  have nonzero : 1 - (t : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr (show (t : ℝ) < 1 from before))
  unfold recoveredSource
  rw [formula, AffineMap.lineMap_apply_module, add_sub_cancel_right, inv_smul_smul₀ nonzero]

/-- Equal recovered sources and targets force equal positions at the recovery time. -/
theorem recoveredSource_position (P : ConvexPolyhedron) (F : P.Face) (t : unitInterval) (before : t < 1)
    (f g : P.BoundaryCurve) (same : P.recoveredSource F t f = P.recoveredSource F t g)
    (target : f 1 = g 1) : P.faceCoordinates F (f t) = P.faceCoordinates F (g t) := by
  have nonzero : (1 - (t : ℝ))⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt (sub_pos.mpr (show (t : ℝ) < 1 from before)))
  change _ • _ = _ • _ at same
  have equal := (smul_right_injective (M := Plane) nonzero) same
  rw [target] at equal
  exact add_right_cancel (by simpa only [sub_eq_add_neg] using equal)

/-- Around any curve, its recovered source is isolated from all other members of the finite source set. -/
theorem recoveredSource_isolation (P : ConvexPolyhedron) (a : Space) (F : P.Face) (t : unitInterval)
    (f : P.BoundaryCurve) : ∃ U : Set P.BoundaryCurve, IsOpen U ∧ f ∈ U ∧
      ∀ g ∈ U, P.recoveredSource F t g ∈ P.sourceImages a F →
        P.recoveredSource F t g = P.recoveredSource F t f := by
  let other := P.sourceImages a F \ {P.recoveredSource F t f}
  refine ⟨P.recoveredSource F t ⁻¹' otherᶜ,
    (P.sourceImages_finite a F).diff.isClosed.isOpen_compl.preimage
      (P.recoveredSource_continuous F t), ?_, ?_⟩
  · exact fun h => h.2 rfl
  · intro g near member
    by_contra different
    exact near ⟨member, different⟩

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Every canonical geodesic's recovered source belongs to the fixed finite source set. -/
theorem recoveredSource_mem (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (F : P.Face) (unique : ∀ G : P.Face, (f 1 : Space) ∈ G.val → G = F)
    (t : unitInterval) (before : t < 1) (inside : (f t : Space) ∈ F.val) :
    P.recoveredSource F t f ∈ P.sourceImages (f 0) F := by
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  have avoids := graph.shortest_lipschitz_avoids_vertices small_faces (P.surfacePathOfCurve f)
    (fun h => different (Subtype.ext h)) shortest finite speed
  obtain ⟨source, member, formula⟩ := (P.surfacePathOfCurve f).source_image_at_face_visit
    shortest finite speed avoids F unique t before inside
  exact P.recoveredSource_eq F t before f source formula ▸ member

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
