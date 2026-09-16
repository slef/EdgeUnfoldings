import SixVertexUnfolding.Geometry.FaceStripTriangleMetric
import SixVertexUnfolding.Geometry.FiniteDevelopmentPatchMetric
import SixVertexUnfolding.Geometry.HingeStripTriangleMetric
import SixVertexUnfolding.Geometry.ConvexSurfaceFolding
import SixVertexUnfolding.Geometry.FiniteDevelopmentFlatMetric
import SixVertexUnfolding.Geometry.FiniteRigidPieces

/-! A compact record of the proved geometry of one radial strip:
its triangle coordinates, inverse distance bound, and exact face-patch metric. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A radial triangle development with its actual surface correspondence and metric guarantees. -/
structure RadialStripTriangle {P : ConvexPolyhedron}
    (routes : C(unitInterval, P.BoundaryCurve)) (p l r : Plane) where
  homeomorph : range (closedRouteStripMap routes) ≃ₜ convexHull ℝ ({p, l, r} : Set Plane)
  radial : ∀ z, (homeomorph ⟨closedRouteStripMap routes z, mem_range_self z⟩ : Plane) = triangleFanMap p l r z
  inverse_nonexpanding : LipschitzWith 1 (fun z => ((homeomorph.symm z).val : Space))
  convex_patches : ∀ (patch : Set Space), Convex ℝ patch →
    ∀ inclusion : C(patch, range (closedRouteStripMap routes)),
      (∀ x, ((inclusion x).val : Space) = (x : Space)) → Isometry (fun x => (homeomorph (inclusion x) : Plane))
  flat_patches : ∀ {z : Space} (chart : P.FlatChart z) (patch : Set Plane), Convex ℝ patch →
    patch ⊆ chart.domain → ∀ inclusion : C(patch, range (closedRouteStripMap routes)),
      (∀ x, ((inclusion x).val : Space) = chart.map (x : Plane)) →
        Isometry (fun x => (homeomorph (inclusion x) : Plane))
  rigid_pieces : HasFiniteRigidPieces (convexHull ℝ ({p, l, r} : Set Plane))
    (fun z => ((homeomorph.symm z).val : Space))

namespace RadialStripTriangle

variable {P : ConvexPolyhedron} {routes : C(unitInterval, P.BoundaryCurve)} {p l r : Plane}
  (D : RadialStripTriangle routes p l r)

/-- A straight segment in the triangle folds to a surface route of no greater length. -/
theorem surface_distance_le (x y : convexHull ℝ ({p, l, r} : Set Plane)) :
    P.surfaceDist (D.homeomorph.symm x).val (D.homeomorph.symm y).val ≤ dist (x : Plane) (y : Plane) :=
  convex_folding_surface_distance _ (convex_convexHull ℝ _)
    ⟨fun z => (D.homeomorph.symm z).val, continuous_subtype_val.comp D.homeomorph.symm.continuous⟩
    D.inverse_nonexpanding x y

end RadialStripTriangle

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem face_strip_development (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (routes : C(unitInterval, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t))
    (F : P.Face)
    (unique_face : ∀ t, ∀ G : P.Face, (T.openEdgeTarget edge t : Space) ∈ G.val → G = F)
    (p : Plane) (terminal : ∀ t : Ioo (0 : ℝ) 1, P.HasTerminalSource (routes (interiorTime t)) F p)
    (noncollinear : ¬ Collinear ℝ ({P.faceCoordinates F u, P.faceCoordinates F v, p} : Set Plane)) :
    Nonempty (RadialStripTriangle routes p (P.faceCoordinates F u) (P.faceCoordinates F v)) := by
  obtain ⟨H, radial, pieces, inverse⟩ := graph.face_strip_triangle_metric small_faces a T edge routes
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

end SixVertexGraph

namespace EdgeFolding

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G) (graph : P.SixVertexGraph)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem hinge_strip_development (shared : P.ShareEdge F G)
    (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (routes : C(unitInterval, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t))
    (on_edge : ∀ t, (T.openEdgeTarget edge t : Space) ∈ F.val ∩ G.val)
    (p : Plane) (terminal : ∀ t : Ioo (0 : ℝ) 1, chart.HasTerminalSource (routes (interiorTime t)) p)
    (noncollinear : ¬ Collinear ℝ ({chart.left u, chart.left v, p} : Set Plane)) :
    Nonempty (RadialStripTriangle routes p (chart.left u) (chart.left v)) := by
  obtain ⟨H, radial, pieces, inverse⟩ := chart.hinge_strip_triangle_metric graph small_faces shared
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

end EdgeFolding
end SixVertexUnfolding.ConvexPolyhedron
