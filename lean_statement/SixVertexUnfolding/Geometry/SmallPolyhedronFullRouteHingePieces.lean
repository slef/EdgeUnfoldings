import SixVertexUnfolding.Geometry.FullRouteHingePieces
import SixVertexUnfolding.Geometry.SmallPolyhedronFullRouteDevelopment

/-! Complete geodesics use the finite rigid face list in joined hinge
coordinates, including routes whose targets lie on the original edge.

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
/-- Every route point has its actual radial coordinates under a finite rigid hinge development. -/
theorem small_full_route_hinge_pieces (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1)
    (only_two : ∀ H : P.Face, (f 1 : Space) ∈ H.val → H = F ∨ H = G)
    (source : Plane) (terminal : chart.HasTerminalSource f source) :
    ∀ t : unitInterval, ∃ piece : chart.DevelopmentPiece,
      (f t : Space) ∈ (chart.pieceFace piece).val ∧
      chart.piecePlace piece (f t) = AffineMap.lineMap source (chart.unfold (f 1)) (t : ℝ) := by
  obtain ⟨code, actual, developed⟩ := small_full_route_development size small_faces f geodesic different
  rcases only_two _ actual.target_in_face with first | second
  · have actual_first : P.HasTerminalSource f F (code.sourceImage (f 0)) := by simpa only [first] using actual
    have same_source := chart.terminal_source_unique f _ source
      (chart.terminal_from_first f _ actual_first) terminal
    intro t
    obtain ⟨i, inside, placed⟩ := developed t
    refine ⟨Sum.inl ⟨⟨code, i⟩, first⟩, inside, ?_⟩
    change chart.firstMotion (code.targetMotion (code.place i (f t))) = _
    rw [placed, AffineMap.apply_lineMap, same_source, first,
      chart.firstMotion_on_face _ actual_first.target_in_face,
      chart.unfold_of_first actual_first.target_in_face]
  · have actual_second : P.HasTerminalSource f G (code.sourceImage (f 0)) := by simpa only [second] using actual
    have same_source := chart.terminal_source_unique f _ source
      (chart.terminal_from_second f _ actual_second) terminal
    intro t
    obtain ⟨i, inside, placed⟩ := developed t
    refine ⟨Sum.inr ⟨⟨code, i⟩, second⟩, inside, ?_⟩
    change chart.secondMotion (code.targetMotion (code.place i (f t))) = _
    rw [placed, AffineMap.apply_lineMap, same_source, second,
      chart.secondMotion_on_face _ actual_second.target_in_face,
      chart.unfold_of_second actual_second.target_in_face]

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
