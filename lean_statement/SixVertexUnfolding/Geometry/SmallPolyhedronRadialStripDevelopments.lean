import SixVertexUnfolding.Geometry.RadialStripDevelopments
import SixVertexUnfolding.Geometry.SmallPolyhedronFaceStripTriangleMetric
import SixVertexUnfolding.Geometry.SmallPolyhedronHingeStripTriangleMetric

/-! A compact record of the proved geometry of one radial strip:
its triangle coordinates, inverse distance bound, and exact face-patch metric.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
theorem small_face_strip_development (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (routes : C(unitInterval, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t))
    (F : P.Face)
    (unique_face : ∀ t, ∀ G : P.Face, (T.openEdgeTarget edge t : Space) ∈ G.val → G = F)
    (p : Plane) (terminal : ∀ t : Ioo (0 : ℝ) 1, P.HasTerminalSource (routes (interiorTime t)) F p)
    (noncollinear : ¬ Collinear ℝ ({P.faceCoordinates F u, P.faceCoordinates F v, p} : Set Plane)) :
    Nonempty (RadialStripTriangle routes p (P.faceCoordinates F u) (P.faceCoordinates F v)) := by
  obtain ⟨H, radial, pieces, inverse⟩ := small_face_strip_triangle_metric size small_faces a T edge routes
    member F unique_face p terminal noncollinear
  refine ⟨⟨H, radial, inverse, finite_development_patch_isometric _ _ H pieces inverse, ?_, ?_⟩⟩
  · intro z
    apply finite_development_flat_patch_isometric _ _ (convex_convexHull ℝ _) H
      (fun piece : P.FaceDevelopmentPiece F => piece.projectedPlace)
      (fun piece => piece.projectedPlace_lipschitz) (fun x => ?_) inverse
    obtain ⟨piece, inside, placed⟩ := pieces x
    exact ⟨piece, placed.symm.trans (piece.projectedPlace_on_face _ inside).symm⟩
  · apply HasFiniteRigidPieces.of_family (fun piece : P.FaceDevelopmentPiece F => piece.lift)
      (fun piece => Isometry.of_dist_eq piece.lift_rigid)
    intro x
    obtain ⟨piece, inside, placed⟩ := pieces (H.symm x)
    rw [H.apply_symm_apply] at placed
    exact ⟨piece, (piece.lift_place _ inside).symm.trans (congrArg piece.lift placed)⟩

end SixVertexUnfolding.ConvexPolyhedron

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G) (size : P.vertices.card ≤ 6)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
theorem small_hinge_strip_development (shared : P.ShareEdge F G)
    (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (routes : C(unitInterval, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t))
    (on_edge : ∀ t, (T.openEdgeTarget edge t : Space) ∈ F.val ∩ G.val)
    (p : Plane) (terminal : ∀ t : Ioo (0 : ℝ) 1, chart.HasTerminalSource (routes (interiorTime t)) p)
    (noncollinear : ¬ Collinear ℝ ({chart.left u, chart.left v, p} : Set Plane)) :
    Nonempty (RadialStripTriangle routes p (chart.left u) (chart.left v)) := by
  obtain ⟨H, radial, pieces, inverse⟩ := chart.small_hinge_strip_triangle_metric size small_faces shared
    a T edge routes member on_edge p terminal noncollinear
  refine ⟨⟨H, radial, inverse, chart.hinge_development_patch_isometric _ _ H pieces inverse, ?_, ?_⟩⟩
  · intro z
    apply finite_development_flat_patch_isometric _ _ (convex_convexHull ℝ _) H
      chart.projectedPiecePlace chart.projectedPiecePlace_lipschitz (fun x => ?_) inverse
    obtain ⟨piece, inside, placed⟩ := pieces x
    exact ⟨piece, placed.symm.trans (chart.projectedPiecePlace_on_face piece _ inside).symm⟩
  · apply HasFiniteRigidPieces.of_family chart.pieceLift
      (fun piece => Isometry.of_dist_eq (chart.pieceLift_rigid piece))
    intro x
    obtain ⟨piece, inside, placed⟩ := pieces (H.symm x)
    rw [H.apply_symm_apply] at placed
    exact ⟨piece, (chart.pieceLift_place piece _ inside).symm.trans
      (congrArg (chart.pieceLift piece) placed)⟩

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
