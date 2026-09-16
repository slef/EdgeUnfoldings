import SixVertexUnfolding.Geometry.StarPolygonBoundary
import SixVertexUnfolding.Geometry.SmallPolyhedronStarCutSegments

/-! The developed star boundary is exactly a finite union of explicit
closed straight segments. Degenerate segments retain all source copies.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter Topology

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

/-- Every listed segment is a cut copy, and every cut copy is on a listed segment. -/
theorem small_cutBoundaryImage_eq_segments {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    charts.cutBoundaryImage = ⋃ e ∈ charts.boundarySegments, segment ℝ e.1 e.2 := by
  ext x
  constructor
  · rintro ⟨d, b, cut, placed⟩
    obtain ⟨s, side, t, at_b, value⟩ := ((charts.global d.adj).places_iff_ray b x).mp placed
    obtain ⟨e, listed, on_segment⟩ := (small_triangle_cut_image size small_faces (charts.global d.adj)
      cofacial side x).mp ⟨s, t, at_b.symm ▸ cut, value⟩
    exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨(charts.mem_boundarySegments e).mpr ⟨d, side, listed⟩, on_segment⟩⟩
  · intro member
    obtain ⟨e, member⟩ := mem_iUnion.mp member
    obtain ⟨listed, on_segment⟩ := mem_iUnion.mp member
    obtain ⟨d, side, listed⟩ := (charts.mem_boundarySegments e).mp listed
    obtain ⟨s, t, cut, value⟩ := (small_triangle_cut_image size small_faces (charts.global d.adj)
      cofacial side x).mpr ⟨e, listed, on_segment⟩
    exact ⟨d, (charts.global d.adj).routes side s t, cut,
      ((charts.global d.adj).places_iff_ray _ _).mpr ⟨s, side, t, rfl, value⟩⟩

/-- The entire boundary is a finite union of whole straight cut segments. -/
theorem small_develop_frontier_eq_segments {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) (separated : charts.KitesSeparated)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    frontier (range (fun c : P.UncutSurface a => charts.develop c.val)) =
      ⋃ e ∈ charts.boundarySegments, segment ℝ e.1 e.2 := by
  rw [small_develop_frontier_eq_cutBoundaryImage size small_faces charts separated cofacial,
    small_cutBoundaryImage_eq_segments size small_faces charts cofacial]

end SixVertexUnfolding.ConvexPolyhedron
