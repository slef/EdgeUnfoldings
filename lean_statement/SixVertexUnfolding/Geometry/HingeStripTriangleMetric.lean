import SixVertexUnfolding.Geometry.ClosedStripHingePieces
import SixVertexUnfolding.Geometry.CutStripTriangleTopology
import SixVertexUnfolding.Geometry.ConvexFiniteSelection

/-! Radial triangles over original hinges have the same metric control
as triangles whose cut edge lies inside one original face. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G) (graph : P.SixVertexGraph)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- A hinge strip has finite rigid face formulas and a nonexpanding planar inverse. -/
theorem hinge_strip_triangle_metric (shared : P.ShareEdge F G)
    (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (routes : C(unitInterval, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t))
    (on_edge : ∀ t, (T.openEdgeTarget edge t : Space) ∈ F.val ∩ G.val)
    (p : Plane) (terminal : ∀ t : Ioo (0 : ℝ) 1, chart.HasTerminalSource (routes (interiorTime t)) p)
    (noncollinear : ¬ Collinear ℝ ({chart.left u, chart.left v, p} : Set Plane)) :
    ∃ H : range (closedRouteStripMap routes) ≃ₜ convexHull ℝ ({p, chart.left u, chart.left v} : Set Plane),
      (∀ z, (H ⟨closedRouteStripMap routes z, mem_range_self z⟩ : Plane) =
        triangleFanMap p (chart.left u) (chart.left v) z) ∧
      (∀ x, ∃ piece : chart.DevelopmentPiece,
        (x.val : Space) ∈ (chart.pieceFace piece).val ∧ chart.piecePlace piece x.val = (H x : Plane)) ∧
      LipschitzWith 1 (fun z => ((H.symm z).val : Space)) := by
  obtain ⟨H, agrees⟩ := graph.closed_strip_triangle_homeomorph_of_noncollinear small_faces
    a T edge p (chart.left u) (chart.left v) noncollinear routes member
  have pieces (x : range (closedRouteStripMap routes)) : ∃ piece : chart.DevelopmentPiece,
      (x.val : Space) ∈ (chart.pieceFace piece).val ∧ chart.piecePlace piece x.val = (H x : Plane) := by
    obtain ⟨z, at_z⟩ := x.property
    obtain ⟨piece, inside, placed⟩ := chart.closed_strip_hinge_pieces graph small_faces shared
      a T edge routes member on_edge p terminal z
    have same : (⟨closedRouteStripMap routes z, mem_range_self z⟩ : range (closedRouteStripMap routes)) = x :=
      Subtype.ext at_z
    refine ⟨piece, by simpa only [at_z] using inside, ?_⟩
    have coordinate := (placed.trans (agrees z).symm).trans (congrArg (fun x => (H x : Plane)) same)
    simpa only [at_z] using coordinate
  refine ⟨H, agrees, pieces, ?_⟩
  apply convex_subtype_finite_selection_lipschitz _ (convex_convexHull ℝ _)
    (fun z => ((H.symm z).val : Space)) (fun piece : chart.DevelopmentPiece => chart.pieceLift piece) 1
    (continuous_subtype_val.comp (continuous_subtype_val.comp H.symm.continuous))
  · intro piece
    exact LipschitzOnWith.of_dist_le_mul (fun z _ w _ => by simpa using (chart.pieceLift_rigid piece z w).le)
  · intro z
    obtain ⟨piece, inside, placed⟩ := pieces (H.symm z)
    refine ⟨piece, ?_⟩
    rw [H.apply_symm_apply] at placed
    exact (chart.pieceLift_place piece _ inside).symm.trans (congrArg (chart.pieceLift piece) placed)

/-- Convex surface patches contained in this hinge development preserve all distances. -/
theorem hinge_development_patch_isometric
    (region : Set (frontier P.body)) (planar : Set Plane) (H : region ≃ₜ planar)
    (pieces : ∀ x, ∃ piece : chart.DevelopmentPiece,
      (x.val : Space) ∈ (chart.pieceFace piece).val ∧ chart.piecePlace piece x.val = (H x : Plane))
    (inverse_bound : LipschitzWith 1 (fun z => ((H.symm z).val : Space)))
    (patch : Set Space) (convex_patch : Convex ℝ patch)
    (inclusion : C(patch, region)) (located : ∀ x, ((inclusion x).val : Space) = (x : Space)) :
    Isometry (fun x => (H (inclusion x) : Plane)) := by
  have forward : LipschitzWith 1 (fun x => (H (inclusion x) : Plane)) := by
    apply convex_subtype_finite_selection_lipschitz patch convex_patch
      (fun x => (H (inclusion x) : Plane)) chart.projectedPiecePlace 1
      (continuous_subtype_val.comp (H.continuous.comp inclusion.continuous))
      (fun piece => (chart.projectedPiecePlace_lipschitz piece).lipschitzOnWith)
    intro x
    obtain ⟨piece, inside, placed⟩ := pieces (inclusion x)
    refine ⟨piece, placed.symm.trans ?_⟩
    exact (chart.projectedPiecePlace_on_face piece _ inside).symm.trans
      (congrArg (chart.projectedPiecePlace piece) (located x))
  apply Isometry.of_dist_eq
  intro x y
  apply le_antisymm
  · simpa using forward.dist_le_mul x y
  · have bound := inverse_bound.dist_le_mul (H (inclusion x)) (H (inclusion y))
    simpa only [H.symm_apply_apply, located, NNReal.coe_one, one_mul] using bound

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
