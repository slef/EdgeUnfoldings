import SixVertexUnfolding.Geometry.OctahedralPatchConstruction
import SixVertexUnfolding.Geometry.PrescribedTrianglePlacement

/-! Realize the petal of a metric patch as a placement of its entire original facet. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.DevelopedPatch

open OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph} {source : Fin 6} {sector : Fin 4}
variable (patch : graph.DevelopedPatch source sector)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

/-- The copied apex and hinge endpoints come from a rigid placement of the actual petal facet. -/
theorem exists_petal_placement : ∃ place : Space →ᵃ[ℝ] Plane,
    place (graph.vertex (fanNeighbor source sector)) = patch.left ∧
    place (graph.vertex (fanNeighbor source (sector + 1))) = patch.right ∧
    place (graph.vertex source) = patch.apex ∧
    ∀ x ∈ (graph.triangleFace small_faces (fanTriangle source sector)).val,
      ∀ y ∈ (graph.triangleFace small_faces (fanTriangle source sector)).val,
        dist (place x) (place y) = dist x y := by
  apply (graph.triangleFace small_faces (fanTriangle source sector)).exists_placement_at_triangle
    (graph.vertex (fanNeighbor source sector)) (graph.vertex (fanNeighbor source (sector + 1))) (graph.vertex source)
  · exact graph.vertex.injective.ne equator_distinct
  · exact graph.vertex.injective.ne (fanNeighbor_ne_source source sector)
  · exact graph.vertex.injective.ne (fanNeighbor_ne_source source (sector + 1))
  · exact graph.fan_sector_on_face source small_faces sector _ (by simp)
  · exact graph.fan_sector_on_face source small_faces sector _ (by simp)
  · exact graph.fan_sector_on_face source small_faces sector _ (by simp)
  · exact patch.hinge_length
  · simpa only [dist_comm] using patch.petal_left
  · simpa only [dist_comm] using patch.petal_right

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.DevelopedPatch
