import SixVertexUnfolding.Geometry.FiniteSourceImages

/-! A finite list of rigid original-face placements in one target
face's coordinate system, independent of the chosen shortest route. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A face portion of one bounded development ending at the prescribed face. -/
def FaceDevelopmentPiece (P : ConvexPolyhedron) (target : P.Face) :=
  {data : Σ code : P.FaceSequence, Fin code.count // data.1.face data.1.last = target}

instance (P : ConvexPolyhedron) (target : P.Face) : Finite (P.FaceDevelopmentPiece target) := by
  unfold FaceDevelopmentPiece
  infer_instance

namespace FaceDevelopmentPiece

variable {P : ConvexPolyhedron} {target : P.Face} (piece : P.FaceDevelopmentPiece target)

def face : P.Face := piece.val.1.face piece.val.2

/-- This original face's rigid placement in the common target coordinates. -/
noncomputable def place : Space →ᵃ[ℝ] Plane :=
  piece.val.1.targetMotion.comp (piece.val.1.place piece.val.2)

theorem rigid (x : Space) (hx : x ∈ piece.face.val) (y : Space) (hy : y ∈ piece.face.val) :
    dist (piece.place x) (piece.place y) = dist x y := by
  change dist (piece.val.1.targetMotion _) (piece.val.1.targetMotion _) = _
  rw [piece.val.1.targetMotion_rigid]
  exact piece.val.1.rigid piece.val.2 x hx y hy

end FaceDevelopmentPiece
end SixVertexUnfolding.ConvexPolyhedron
