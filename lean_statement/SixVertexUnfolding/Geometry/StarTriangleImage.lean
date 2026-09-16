import SixVertexUnfolding.Geometry.StarCutEndpoints
import SixVertexUnfolding.Geometry.StarDevelopmentMap
import SixVertexUnfolding.Geometry.RadialStripInterior
import SixVertexUnfolding.Geometry.PlacedTriangleGeometry

/-! Every open triangle of the actual kite construction is present
in the developed retained surface. No star cut removes its interior. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

/-- Interior triangle points lie on positive rays ending at nonvertex cut points. -/
theorem placed_triangle_interior_uncut {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (D : PlacedCutEdgeTriangles T edge)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (side : Bool) (b : frontier P.body) (inside : b ∈ range (closedRouteStripMap (D.routes side)))
    (interior_point : ((D.sideTriangle side).homeomorph ⟨b, inside⟩ : Plane) ∈ interior (D.sideRegion side)) :
    b ∉ P.starCuts a := by
  have represented := inside
  obtain ⟨z, at_b⟩ := represented
  have same : (⟨closedRouteStripMap (D.routes side) z, mem_range_self z⟩ :
      range (closedRouteStripMap (D.routes side))) = ⟨b, inside⟩ := Subtype.ext at_b
  have coordinate := (D.sideTriangle side).radial z
  rw [same] at coordinate
  rw [coordinate] at interior_point
  obtain ⟨sp, sb, tp, _⟩ := (triangleFan_interior_iff _ _ _ (D.side_noncollinear side) z).mp interior_point
  have nonvertex : (T.closedEdgeTarget edge z.1 : Space) ∉ P.vertices :=
    T.openEdgeTarget_nonvertex edge ⟨z.1, sp, sb⟩
  have outside := graph.nonvertex_terminal_ray_uncut small_faces a (T.closedEdgeTarget edge z.1)
    cofacial (T.closedEdgeTarget_cut edge z.1) nonvertex (D.routes side z.1)
    (D.routes_member side z.1) z.2 tp
  change D.routes side z.1 z.2 = b at at_b
  rwa [at_b] at outside

/-- The whole open planar triangle belongs to the image of the actual star map. -/
theorem triangle_interior_subset_develop_range {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v : T.vertices} (edge : T.graph.Adj u v) (side : Bool) :
    interior ((charts.global edge).sideRegion side) ⊆
      range (fun b : P.UncutSurface a => charts.develop b.val) := by
  intro x interior_x
  let D := charts.global edge
  let z : D.sideRegion side := ⟨x, interior_subset interior_x⟩
  let b := (D.sideTriangle side).homeomorph.symm z
  have coordinate : ((D.sideTriangle side).homeomorph b : Plane) = x :=
    congrArg Subtype.val ((D.sideTriangle side).homeomorph.apply_symm_apply z)
  have outside := graph.placed_triangle_interior_uncut small_faces D cofacial side b.val b.property
    (coordinate.symm ▸ interior_x)
  refine ⟨⟨b.val, outside⟩, ?_⟩
  exact graph.develop_agrees small_faces charts cofacial edge outside ⟨side, b.property, coordinate⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
