import SixVertexUnfolding.Geometry.ClosedStripHingePieces
import SixVertexUnfolding.Geometry.SmallPolyhedronFullRouteHingePieces

/-! Closed radial strips over original hinges use finitely many rigid
face placements in their common two-face coordinates.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G) (size : P.vertices.card ≤ 6)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- The finite hinge formulas hold on the complete closed radial square. -/
theorem small_closed_strip_hinge_pieces (shared : P.ShareEdge F G)
    (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (routes : C(unitInterval, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t))
    (on_edge : ∀ t, (T.openEdgeTarget edge t : Space) ∈ F.val ∩ G.val)
    (p : Plane) (terminal : ∀ t : Ioo (0 : ℝ) 1, chart.HasTerminalSource (routes (interiorTime t)) p) :
    ∀ z, ∃ piece : chart.DevelopmentPiece,
      (closedRouteStripMap routes z : Space) ∈ (chart.pieceFace piece).val ∧
      chart.piecePlace piece (closedRouteStripMap routes z) = triangleFanMap p (chart.left u) (chart.left v) z := by
  let surface := closedRouteStripMap routes
  let planar := triangleFanMap p (chart.left u) (chart.left v)
  let good (piece : chart.DevelopmentPiece) : Set (unitInterval × unitInterval) :=
    {z | (surface z : Space) ∈ (chart.pieceFace piece).val ∧ chart.piecePlace piece (surface z) = planar z}
  have surface_cont : Continuous (fun z => (surface z : Space)) :=
    continuous_subtype_val.comp surface.continuous
  have closed (piece : chart.DevelopmentPiece) : IsClosed (good piece) :=
    ((chart.pieceFace piece).isClosed.preimage surface_cont).inter
      (isClosed_eq ((chart.piecePlace piece).continuous_of_finiteDimensional.comp surface_cont) planar.continuous)
  let inclusion : Ioo (0 : ℝ) 1 × unitInterval → unitInterval × unitInterval := Prod.map interiorTime id
  have dense : DenseRange inclusion := interiorTime_dense.prodMap denseRange_id
  have interior (z : Ioo (0 : ℝ) 1 × unitInterval) : inclusion z ∈ ⋃ piece, good piece := by
    have start : routes (interiorTime z.1) 0 = a := congrArg Prod.fst (member _).2
    have finish : routes (interiorTime z.1) 1 = T.openEdgeTarget edge z.1 := congrArg Prod.snd (member _).2
    obtain ⟨patch⟩ := chart.exists_metric_patch shared (on_edge z.1) (T.openEdgeTarget_nonvertex edge z.1)
    obtain ⟨piece, inside, placed⟩ := chart.small_full_route_hinge_pieces size small_faces
      (routes (interiorTime z.1)) (member _).1
      (by simpa only [start, finish] using T.openEdgeTarget_different edge z.1)
      (by simpa only [finish] using patch.only_two _ patch.center_mem) p (terminal z.1) z.2
    refine mem_iUnion.mpr ⟨piece, inside, ?_⟩
    change chart.piecePlace piece (routes (interiorTime z.1) z.2) =
      AffineMap.lineMap p (AffineMap.lineMap (chart.left u) (chart.left v) (z.1 : ℝ)) (z.2 : ℝ)
    rw [placed, finish, chart.unfold_of_first (on_edge z.1).1, ← AffineMap.apply_lineMap]
    rfl
  intro z
  have covered : z ∈ ⋃ piece, good piece := dense.induction_on z (isClosed_iUnion_of_finite closed) interior
  exact mem_iUnion.mp covered

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
