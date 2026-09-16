import SixVertexUnfolding.Geometry.FaceDevelopmentPieces
import SixVertexUnfolding.Geometry.FacetNonexpandingExtension

/-! The finite face placements may be extended by orthogonal projection.
These extensions agree on their faces and do not stretch ambient space. -/

namespace SixVertexUnfolding.ConvexPolyhedron.FaceDevelopmentPiece

open Set

variable {P : ConvexPolyhedron} {target : P.Face} (piece : P.FaceDevelopmentPiece target)

/-- Orthogonally project onto the face plane, then use the prescribed rigid placement. -/
noncomputable def projectedPlace : Space → Plane :=
  Classical.choose (piece.face.exists_nonexpanding_extension piece.place piece.rigid)

theorem projectedPlace_lipschitz : LipschitzWith 1 piece.projectedPlace :=
  (Classical.choose_spec (piece.face.exists_nonexpanding_extension piece.place piece.rigid)).1

theorem projectedPlace_on_face (x : Space) (hx : x ∈ piece.face.val) :
    piece.projectedPlace x = piece.place x :=
  (Classical.choose_spec (piece.face.exists_nonexpanding_extension piece.place piece.rigid)).2 hx

end SixVertexUnfolding.ConvexPolyhedron.FaceDevelopmentPiece
