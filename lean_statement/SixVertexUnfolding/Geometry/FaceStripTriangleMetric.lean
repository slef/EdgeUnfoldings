import SixVertexUnfolding.Geometry.ClosedStripFacePieces
import SixVertexUnfolding.Geometry.CutStripTriangleTopology
import SixVertexUnfolding.Geometry.ConvexFiniteSelection

/-! The actual radial triangle map for a cut edge inside an original face
uses rigid face pieces. Its inverse cannot increase Euclidean distances. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The radial homeomorphism has finitely many rigid face formulas and a nonexpanding inverse. -/
theorem face_strip_triangle_metric (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (routes : C(unitInterval, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t))
    (F : P.Face)
    (unique_face : ∀ t, ∀ G : P.Face, (T.openEdgeTarget edge t : Space) ∈ G.val → G = F)
    (p : Plane) (terminal : ∀ t : Ioo (0 : ℝ) 1, P.HasTerminalSource (routes (interiorTime t)) F p)
    (noncollinear : ¬ Collinear ℝ ({P.faceCoordinates F u, P.faceCoordinates F v, p} : Set Plane)) :
    ∃ H : range (closedRouteStripMap routes) ≃ₜ
        convexHull ℝ ({p, P.faceCoordinates F u, P.faceCoordinates F v} : Set Plane),
      (∀ z, (H ⟨closedRouteStripMap routes z, mem_range_self z⟩ : Plane) =
        triangleFanMap p (P.faceCoordinates F u) (P.faceCoordinates F v) z) ∧
      (∀ x, ∃ piece : P.FaceDevelopmentPiece F,
        (x.val : Space) ∈ piece.face.val ∧ piece.place x.val = (H x : Plane)) ∧
      LipschitzWith 1 (fun z => ((H.symm z).val : Space)) := by
  obtain ⟨H, agrees⟩ := graph.closed_strip_triangle_homeomorph_of_noncollinear small_faces
    a T edge p (P.faceCoordinates F u) (P.faceCoordinates F v) noncollinear routes member
  have pieces (x : range (closedRouteStripMap routes)) : ∃ piece : P.FaceDevelopmentPiece F,
      (x.val : Space) ∈ piece.face.val ∧ piece.place x.val = (H x : Plane) := by
    obtain ⟨z, at_z⟩ := x.property
    obtain ⟨piece, inside, placed⟩ := graph.closed_strip_face_pieces small_faces a T edge routes
      member F unique_face p terminal z
    have same : (⟨closedRouteStripMap routes z, mem_range_self z⟩ : range (closedRouteStripMap routes)) = x :=
      Subtype.ext at_z
    refine ⟨piece, by simpa only [at_z] using inside, ?_⟩
    have coordinate := (placed.trans (agrees z).symm).trans (congrArg (fun x => (H x : Plane)) same)
    simpa only [at_z] using coordinate
  refine ⟨H, agrees, pieces, ?_⟩
  apply convex_subtype_finite_selection_lipschitz _ (convex_convexHull ℝ _)
    (fun z => ((H.symm z).val : Space)) (fun piece : P.FaceDevelopmentPiece F => piece.lift) 1
    (continuous_subtype_val.comp (continuous_subtype_val.comp H.symm.continuous))
  · intro piece
    exact LipschitzOnWith.of_dist_le_mul (fun z _ w _ => by simpa using (piece.lift_rigid z w).le)
  · intro z
    obtain ⟨piece, inside, placed⟩ := pieces (H.symm z)
    refine ⟨piece, ?_⟩
    rw [H.apply_symm_apply] at placed
    exact (piece.lift_place _ inside).symm.trans (congrArg piece.lift placed)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
