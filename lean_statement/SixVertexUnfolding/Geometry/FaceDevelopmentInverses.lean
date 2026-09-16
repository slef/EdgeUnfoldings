import SixVertexUnfolding.Geometry.FaceDevelopmentPieces
import SixVertexUnfolding.Geometry.FacetPlaneInverse

/-! Every finite original-face placement has a rigid inverse plane map.
These maps will fold the planar radial triangles back onto the surface. -/

namespace SixVertexUnfolding.ConvexPolyhedron.FaceDevelopmentPiece

open Set

variable {P : ConvexPolyhedron} {target : P.Face} (piece : P.FaceDevelopmentPiece target)

/-- The rigid lift from target coordinates to the plane of this original face. -/
noncomputable def lift : Plane →ᵃ[ℝ] Space :=
  Classical.choose (piece.face.exists_rigid_plane_inverse piece.place piece.rigid)

theorem lift_rigid (z w : Plane) : dist (piece.lift z) (piece.lift w) = dist z w :=
  (Classical.choose_spec (piece.face.exists_rigid_plane_inverse piece.place piece.rigid)).2.2.2 z w

theorem lift_place (x : Space) (hx : x ∈ piece.face.val) : piece.lift (piece.place x) = x :=
  (Classical.choose_spec (piece.face.exists_rigid_plane_inverse piece.place piece.rigid)).2.2.1 x
    (subset_affineSpan ℝ _ hx)

theorem place_lift (z : Plane) : piece.place (piece.lift z) = z :=
  (Classical.choose_spec (piece.face.exists_rigid_plane_inverse piece.place piece.rigid)).2.1 z

end SixVertexUnfolding.ConvexPolyhedron.FaceDevelopmentPiece
