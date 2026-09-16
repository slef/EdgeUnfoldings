import SixVertexUnfolding.Geometry.StarCutBoundary
import SixVertexUnfolding.Geometry.TriangleBoundary

/-! The planar boundary consists exactly of the represented star-cut
copies and is contained in finitely many straight triangle edges. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutTreeCharts

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)

/-- Keep every planar copy of a cut point, since the two sides need not coincide. -/
def cutBoundaryImage : Set Plane :=
  {x | ∃ d : T.graph.Dart, ∃ b : frontier P.body, b ∈ P.starCuts a ∧ (charts.global d.adj).Places b x}

/-- Each point of the closed polygon union has an actual surface preimage in one of its triangles. -/
theorem closedImage_has_placement {x : Plane} (member : x ∈ charts.closedImage) :
    ∃ d : T.graph.Dart, ∃ b : frontier P.body, (charts.global d.adj).Places b x := by
  obtain ⟨d, member⟩ := mem_iUnion.mp member
  have side_exists : ∃ side : Bool, x ∈ (charts.global d.adj).sideRegion side := by
    rcases member with first | second
    · exact ⟨false, first⟩
    · exact ⟨true, second⟩
  obtain ⟨side, inside⟩ := side_exists
  let b := ((charts.global d.adj).sideTriangle side).homeomorph.symm ⟨x, inside⟩
  exact ⟨d, b.val, side, b.property,
    congrArg Subtype.val (((charts.global d.adj).sideTriangle side).homeomorph.apply_symm_apply ⟨x, inside⟩)⟩

end CutTreeCharts

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

/-- The complete planar boundary is exactly the image of all labelled cut-side copies. -/
theorem develop_frontier_eq_cutBoundaryImage {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    frontier (range (fun c : P.UncutSurface a => charts.develop c.val)) = charts.cutBoundaryImage := by
  ext x
  constructor
  · intro boundary
    have in_closed := frontier_subset_closure boundary
    rw [graph.closure_develop_range_eq_closedImage small_faces charts cofacial] at in_closed
    obtain ⟨d, b, placed⟩ := charts.closedImage_has_placement in_closed
    exact ⟨d, b, (graph.placement_boundary_iff_cut small_faces charts source at_source cofacial d.adj placed).mp boundary, placed⟩
  · rintro ⟨d, b, cut, placed⟩
    exact (graph.placement_boundary_iff_cut small_faces charts source at_source cofacial d.adj placed).mpr cut

/-- Every boundary point lies on one of the finitely many actual triangle edges. -/
theorem develop_frontier_on_triangle_edges {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {x : Plane} (boundary : x ∈ frontier (range (fun c : P.UncutSurface a => charts.develop c.val))) :
    ∃ d : T.graph.Dart, ∃ side : Bool,
      let D := charts.global d.adj
      x ∈ segment ℝ (D.motion (D.apex side)) (D.motion D.model.left) ∪
        (segment ℝ (D.motion (D.apex side)) (D.motion D.model.right) ∪
          segment ℝ (D.motion D.model.left) (D.motion D.model.right)) := by
  have in_closed := frontier_subset_closure boundary
  rw [graph.closure_develop_range_eq_closedImage small_faces charts cofacial] at in_closed
  obtain ⟨d, b, side, inside, value⟩ := charts.closedImage_has_placement in_closed
  let D := charts.global d.adj
  have member : x ∈ D.sideRegion side := value ▸ ((D.sideTriangle side).homeomorph ⟨b, inside⟩).property
  have not_interior : x ∉ interior (D.sideRegion side) := by
    intro interior_x
    have in_range := graph.triangle_interior_subset_develop_range small_faces charts cofacial d.adj side interior_x
    have open_range := (graph.develop_isOpenEmbedding small_faces charts source at_source cofacial).isOpen_range
    exact boundary.2 (open_range.interior_eq.symm ▸ in_range)
  exact ⟨d, side, triangle_frontier_subset_edges _ _ _ (D.side_noncollinear side)
    ⟨subset_closure member, not_interior⟩⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
