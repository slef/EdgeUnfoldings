import SixVertexUnfolding.Geometry.FullRouteDevelopment
import SixVertexUnfolding.Geometry.FaceDevelopmentPieces

/-! One fixed finite development supplies every point of a shortest
route in its actual terminal source coordinates, not only its final tail. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Every route point is the inverse image of its radial planar point under a member of one finite rigid list. -/
theorem full_route_developed_pieces (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (F : P.Face)
    (unique_face : ∀ G : P.Face, (f 1 : Space) ∈ G.val → G = F)
    (source : Plane) (terminal : P.HasTerminalSource f F source) :
    ∀ t : unitInterval, ∃ piece : P.FaceDevelopmentPiece F,
      (f t : Space) ∈ piece.face.val ∧
      piece.place (f t) = AffineMap.lineMap source (P.faceCoordinates F (f 1)) (t : ℝ) := by
  obtain ⟨code, actual, developed⟩ := graph.full_route_development small_faces f geodesic different
  have same_face := unique_face _ actual.target_in_face
  have actual' : P.HasTerminalSource f F (code.sourceImage (f 0)) := by simpa only [same_face] using actual
  have same_source := actual'.unique terminal
  intro t
  obtain ⟨i, inside, placed⟩ := developed t
  refine ⟨⟨⟨code, i⟩, same_face⟩, inside, ?_⟩
  change code.targetMotion (code.place i (f t)) = _
  simpa only [same_face, same_source] using placed

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
