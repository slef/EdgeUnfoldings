import SixVertexUnfolding.Geometry.StarCutSegments

/-! The developed star boundary is exactly a finite union of explicit
closed straight segments. Degenerate segments retain all source copies. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutTreeCharts

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)

/-- Collect the cut sides in the single global placement. -/
noncomputable def boundarySegments : Finset (Plane × Plane) := by
  classical
  letI : Fintype T.vertices := T.finite_vertices.fintype
  letI : DecidableRel T.graph.Adj := Classical.decRel _
  exact Finset.univ.biUnion (fun d : T.graph.Dart =>
    Finset.univ.biUnion (fun side : Bool => (charts.global d.adj).cutSegments side))

theorem mem_boundarySegments (e : Plane × Plane) :
    e ∈ charts.boundarySegments ↔ ∃ d : T.graph.Dart, ∃ side : Bool,
      e ∈ (charts.global d.adj).cutSegments side := by
  classical
  simp [boundarySegments, or_comm]

end CutTreeCharts

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

/-- Every listed segment is a cut copy, and every cut copy is on a listed segment. -/
theorem cutBoundaryImage_eq_segments {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    charts.cutBoundaryImage = ⋃ e ∈ charts.boundarySegments, segment ℝ e.1 e.2 := by
  ext x
  constructor
  · rintro ⟨d, b, cut, placed⟩
    obtain ⟨s, side, t, at_b, value⟩ := ((charts.global d.adj).places_iff_ray b x).mp placed
    obtain ⟨e, listed, on_segment⟩ := (graph.triangle_cut_image small_faces (charts.global d.adj)
      cofacial side x).mp ⟨s, t, at_b.symm ▸ cut, value⟩
    exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨(charts.mem_boundarySegments e).mpr ⟨d, side, listed⟩, on_segment⟩⟩
  · intro member
    obtain ⟨e, member⟩ := mem_iUnion.mp member
    obtain ⟨listed, on_segment⟩ := mem_iUnion.mp member
    obtain ⟨d, side, listed⟩ := (charts.mem_boundarySegments e).mp listed
    obtain ⟨s, t, cut, value⟩ := (graph.triangle_cut_image small_faces (charts.global d.adj)
      cofacial side x).mpr ⟨e, listed, on_segment⟩
    exact ⟨d, (charts.global d.adj).routes side s t, cut,
      ((charts.global d.adj).places_iff_ray _ _).mpr ⟨s, side, t, rfl, value⟩⟩

/-- The entire boundary is a finite union of whole straight cut segments. -/
theorem develop_frontier_eq_segments {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    frontier (range (fun c : P.UncutSurface a => charts.develop c.val)) =
      ⋃ e ∈ charts.boundarySegments, segment ℝ e.1 e.2 := by
  rw [graph.develop_frontier_eq_cutBoundaryImage small_faces charts source at_source cofacial,
    graph.cutBoundaryImage_eq_segments small_faces charts cofacial]

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
