import SixVertexUnfolding.Geometry.FaceDevelopmentPieces
import SixVertexUnfolding.Geometry.EdgeSourceImages
import SixVertexUnfolding.Geometry.FacetPlaneInverse
import SixVertexUnfolding.Geometry.FacetNonexpandingExtension

/-! The two finite face-development lists in the joined coordinates
of an original edge. Each entry still places one whole original face rigidly. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G)

/-- Developments ending at either of the two incident faces. -/
abbrev DevelopmentPiece (_chart : EdgeFolding facets F G) := P.FaceDevelopmentPiece F ⊕ P.FaceDevelopmentPiece G

def pieceFace : chart.DevelopmentPiece → P.Face
  | .inl piece => piece.face
  | .inr piece => piece.face

noncomputable def piecePlace : chart.DevelopmentPiece → Space →ᵃ[ℝ] Plane
  | .inl piece => chart.firstMotion.comp piece.place
  | .inr piece => chart.secondMotion.comp piece.place

theorem piece_rigid (piece : chart.DevelopmentPiece) (x : Space) (hx : x ∈ (chart.pieceFace piece).val)
    (y : Space) (hy : y ∈ (chart.pieceFace piece).val) :
    dist (chart.piecePlace piece x) (chart.piecePlace piece y) = dist x y := by
  cases piece with
  | inl piece => exact (chart.firstMotion_rigid _ _).trans (piece.rigid x hx y hy)
  | inr piece => exact (chart.secondMotion_rigid _ _).trans (piece.rigid x hx y hy)

noncomputable def pieceLift (piece : chart.DevelopmentPiece) : Plane →ᵃ[ℝ] Space :=
  Classical.choose ((chart.pieceFace piece).exists_rigid_plane_inverse (chart.piecePlace piece) (chart.piece_rigid piece))

theorem pieceLift_rigid (piece : chart.DevelopmentPiece) (z w : Plane) :
    dist (chart.pieceLift piece z) (chart.pieceLift piece w) = dist z w :=
  (Classical.choose_spec ((chart.pieceFace piece).exists_rigid_plane_inverse (chart.piecePlace piece)
    (chart.piece_rigid piece))).2.2.2 z w

theorem pieceLift_place (piece : chart.DevelopmentPiece) (x : Space) (hx : x ∈ (chart.pieceFace piece).val) :
    chart.pieceLift piece (chart.piecePlace piece x) = x :=
  (Classical.choose_spec ((chart.pieceFace piece).exists_rigid_plane_inverse (chart.piecePlace piece)
    (chart.piece_rigid piece))).2.2.1 x (subset_affineSpan ℝ _ hx)

noncomputable def projectedPiecePlace (piece : chart.DevelopmentPiece) : Space → Plane :=
  Classical.choose ((chart.pieceFace piece).exists_nonexpanding_extension (chart.piecePlace piece) (chart.piece_rigid piece))

theorem projectedPiecePlace_lipschitz (piece : chart.DevelopmentPiece) :
    LipschitzWith 1 (chart.projectedPiecePlace piece) :=
  (Classical.choose_spec ((chart.pieceFace piece).exists_nonexpanding_extension (chart.piecePlace piece)
    (chart.piece_rigid piece))).1

theorem projectedPiecePlace_on_face (piece : chart.DevelopmentPiece) (x : Space)
    (hx : x ∈ (chart.pieceFace piece).val) : chart.projectedPiecePlace piece x = chart.piecePlace piece x :=
  (Classical.choose_spec ((chart.pieceFace piece).exists_nonexpanding_extension (chart.piecePlace piece)
    (chart.piece_rigid piece))).2 hx

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
