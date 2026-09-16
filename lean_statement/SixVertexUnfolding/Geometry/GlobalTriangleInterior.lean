import SixVertexUnfolding.Geometry.PlacedTriangleGeometry
import SixVertexUnfolding.Geometry.GlobalKiteSeparation
import SixVertexUnfolding.Geometry.StarDevelopmentMap

/-! Nonoverlap identifies the actual preimage of every point in a
developed triangle interior, across the entire chart collection. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces

/-- An interior triangle point has exactly its original surface preimage, even among all other kites. -/
theorem global_triangle_interior_unique {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    {u v w z : T.vertices} (first : T.graph.Adj u v) (second : T.graph.Adj w z) (side : Bool)
    {b c : frontier P.body}
    (inside : b ∈ range (closedRouteStripMap ((charts.global first).routes side)))
    (interior_point : (((charts.global first).sideTriangle side).homeomorph ⟨b, inside⟩ : Plane) ∈
      interior ((charts.global first).sideRegion side))
    (other : (charts.global second).Places c
      (((charts.global first).sideTriangle side).homeomorph ⟨b, inside⟩)) : b = c := by
  by_cases same : s(u, v) = s(w, z)
  · rcases Sym2.eq_iff.mp same with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (charts.global first).interior_placement_unique side inside interior_point other
    · have reversed := (charts.places_reverse second c _).mp other
      exact (charts.global first).interior_placement_unique side inside interior_point reversed
  · have excluded := graph.global_kites_nonoverlap small_faces T charts source at_source second first (Ne.symm same)
    have in_first : (((charts.global first).sideTriangle side).homeomorph ⟨b, inside⟩ : Plane) ∈
        interior (charts.kite first) := interior_mono ((charts.global first).side_subset_kite side) interior_point
    have in_second := (charts.global second).places_mem_kite other
    exact (disjoint_left.mp excluded in_second in_first).elim

/-- The assembled development is injective at every point lying in an open developed triangle. -/
theorem develop_injective_at_triangle_interior {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v : T.vertices} (edge : T.graph.Adj u v) (side : Bool) (b c : P.UncutSurface a)
    (inside : b.val ∈ range (closedRouteStripMap ((charts.global edge).routes side)))
    (interior_point : (((charts.global edge).sideTriangle side).homeomorph ⟨b.val, inside⟩ : Plane) ∈
      interior ((charts.global edge).sideRegion side))
    (same : charts.develop b.val = charts.develop c.val) : b = c := by
  apply Subtype.ext
  have at_b := graph.develop_on_triangle small_faces charts cofacial edge side b.val inside b.property
  obtain ⟨w, z, other, placed⟩ := charts.develop_spec c.val
  rw [← same, at_b] at placed
  exact graph.global_triangle_interior_unique small_faces charts source at_source edge other side inside interior_point placed

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
