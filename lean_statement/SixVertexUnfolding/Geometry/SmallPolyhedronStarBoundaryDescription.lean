import SixVertexUnfolding.Geometry.StarBoundaryDescription
import SixVertexUnfolding.Geometry.SmallPolyhedronStarCutBoundary

/-! The planar boundary consists exactly of the represented star-cut
copies and is contained in finitely many straight triangle edges.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter Topology

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

/-- The complete planar boundary is exactly the image of all labelled cut-side copies. -/
theorem small_develop_frontier_eq_cutBoundaryImage {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) (separated : charts.KitesSeparated)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    frontier (range (fun c : P.UncutSurface a => charts.develop c.val)) = charts.cutBoundaryImage := by
  ext x
  constructor
  · intro boundary
    have in_closed := frontier_subset_closure boundary
    rw [small_closure_develop_range_eq_closedImage size small_faces charts cofacial] at in_closed
    obtain ⟨d, b, placed⟩ := charts.closedImage_has_placement in_closed
    exact ⟨d, b, (small_placement_boundary_iff_cut size small_faces charts separated cofacial d.adj placed).mp boundary, placed⟩
  · rintro ⟨d, b, cut, placed⟩
    exact (small_placement_boundary_iff_cut size small_faces charts separated cofacial d.adj placed).mpr cut

/-- Every boundary point lies on one of the finitely many actual triangle edges. -/
theorem small_develop_frontier_on_triangle_edges {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) (separated : charts.KitesSeparated)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {x : Plane} (boundary : x ∈ frontier (range (fun c : P.UncutSurface a => charts.develop c.val))) :
    ∃ d : T.graph.Dart, ∃ side : Bool,
      let D := charts.global d.adj
      x ∈ segment ℝ (D.motion (D.apex side)) (D.motion D.model.left) ∪
        (segment ℝ (D.motion (D.apex side)) (D.motion D.model.right) ∪
          segment ℝ (D.motion D.model.left) (D.motion D.model.right)) := by
  have in_closed := frontier_subset_closure boundary
  rw [small_closure_develop_range_eq_closedImage size small_faces charts cofacial] at in_closed
  obtain ⟨d, b, side, inside, value⟩ := charts.closedImage_has_placement in_closed
  let D := charts.global d.adj
  have member : x ∈ D.sideRegion side := value ▸ ((D.sideTriangle side).homeomorph ⟨b, inside⟩).property
  have not_interior : x ∉ interior (D.sideRegion side) := by
    intro interior_x
    have in_range := small_triangle_interior_subset_develop_range size small_faces charts cofacial d.adj side interior_x
    have open_range := (small_develop_isOpenEmbedding size small_faces charts separated cofacial).isOpen_range
    exact boundary.2 (open_range.interior_eq.symm ▸ in_range)
  exact ⟨d, side, triangle_frontier_subset_edges _ _ _ (D.side_noncollinear side)
    ⟨subset_closure member, not_interior⟩⟩

end SixVertexUnfolding.ConvexPolyhedron
