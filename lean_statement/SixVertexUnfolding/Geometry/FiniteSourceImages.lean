import SixVertexUnfolding.Geometry.FiniteFaceSequences
import SixVertexUnfolding.Geometry.FacetCoordinateChange

/-! The bounded developments give finitely many source copies in the fixed
coordinates of any target face. Endpoint coordinates are no longer mixed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace FaceSequence

variable {P : ConvexPolyhedron} (code : P.FaceSequence)

private theorem target_motion_exists :
    ∃ motion : Plane →ᵃ[ℝ] Plane,
      (∀ x y, dist (motion x) (motion y) = dist x y) ∧
      ∀ x ∈ (code.face code.last).val,
        motion (code.place code.last x) = P.faceCoordinates (code.face code.last) x :=
  (code.face code.last).exists_coordinate_change (code.place code.last)
    (P.faceCoordinates (code.face code.last)) (code.rigid code.last)
    (P.faceCoordinates_rigid (code.face code.last))

/-- Move this development into the fixed coordinates of its final facet. -/
noncomputable def targetMotion : Plane →ᵃ[ℝ] Plane := code.target_motion_exists.choose

theorem targetMotion_rigid (x y : Plane) : dist (code.targetMotion x) (code.targetMotion y) = dist x y :=
  code.target_motion_exists.choose_spec.1 x y

theorem targetMotion_on_face (x : Space) (hx : x ∈ (code.face code.last).val) :
    code.targetMotion (code.place code.last x) = P.faceCoordinates (code.face code.last) x :=
  code.target_motion_exists.choose_spec.2 x hx

/-- The source copy of this developed face sequence. -/
noncomputable def sourceImage (a : Space) : Plane := code.targetMotion (code.place code.first a)

theorem distanceValue_eq_source_distance (a b : Space) (hb : b ∈ (code.face code.last).val) :
    code.distanceValue a b = dist (code.sourceImage a) (P.faceCoordinates (code.face code.last) b) := by
  rw [sourceImage, ← code.targetMotion_on_face b hb, code.targetMotion_rigid]
  rfl

end FaceSequence

/-- All source copies in the fixed target-face coordinates, from bounded face sequences ending there. -/
def sourceImages (P : ConvexPolyhedron) (a : Space) (F : P.Face) : Set Plane :=
  range (fun code : {code : P.FaceSequence // code.face code.last = F} => code.val.sourceImage a)

theorem sourceImages_finite (P : ConvexPolyhedron) (a : Space) (F : P.Face) :
    (P.sourceImages a F).Finite := Set.finite_range _

end SixVertexUnfolding.ConvexPolyhedron
