import SixVertexUnfolding.Geometry.PrismDiagonalFallback
import SixVertexUnfolding.Geometry.FaceCornerCones
import SixVertexUnfolding.Geometry.TriangleCones
import SixVertexUnfolding.Geometry.TriangleAngles

/-! Every original prism face lies in its full corner cone, including at a
cut vertex. Both generators are original edges of the whole face. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel EuclideanGeometry

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4}
variable (prism_kind : graph.kind = .prismDiagonal)
variable (net : graph.PrismFallbackDevelopment small_faces)
include prism_kind

/-- Supporting facets at the two original edges contain the entire placed face. -/
theorem PrismFallbackDevelopment.face_subset_corner_cone (f : FaceLabel) (i : Fin 6)
    (member : i ∈ faceVertices f) :
    net.place f '' (graph.prismDiagonalFace small_faces f).val ⊆
      translatedCone (net.place f (graph.prismVertex i))
        (net.place f (graph.prismVertex (neighbors f i).1) - net.place f (graph.prismVertex i))
        (net.place f (graph.prismVertex (neighbors f i).2) - net.place f (graph.prismVertex i)) := by
  obtain ⟨l, r, aL, bL, cL, aR, cR, bR⟩ := (by decide : ∀ f i, i ∈ faceVertices f →
    ∃ l r : FaceLabel,
      i ∈ faceVertices l ∧ (neighbors f i).1 ∈ faceVertices l ∧ (neighbors f i).2 ∉ faceVertices l ∧
      i ∈ faceVertices r ∧ (neighbors f i).2 ∈ faceVertices r ∧ (neighbors f i).1 ∉ faceVertices r) f i member
  have corners := (by decide : ∀ f i, i ∈ faceVertices f →
    (neighbors f i).1 ∈ faceVertices f ∧ (neighbors f i).2 ∈ faceVertices f ∧
    i ≠ (neighbors f i).1 ∧ i ≠ (neighbors f i).2 ∧ (neighbors f i).1 ≠ (neighbors f i).2) f i member
  have on_face (g : FaceLabel) (j : Fin 6) := graph.prismVertex_mem_face small_faces prism_kind g j
  have noncollinear := P.no_three_collinear_vertices (graph.prismVertex i).property
    (graph.prismVertex (neighbors f i).1).property (graph.prismVertex (neighbors f i).2).property
    (graph.prismVertex_injective.ne corners.2.2.1) (graph.prismVertex_injective.ne corners.2.2.2.1)
    (graph.prismVertex_injective.ne corners.2.2.2.2)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨t, u, ht, hu, coords⟩ := (graph.prismDiagonalFace small_faces f).nonnegative_corner_coordinates_of_facets
    (graph.prismDiagonalFace small_faces l) (graph.prismDiagonalFace small_faces r)
    (graph.prismVertex i) (graph.prismVertex (neighbors f i).1) (graph.prismVertex (neighbors f i).2) x
    ((on_face _ _).mpr member) ((on_face _ _).mpr corners.1) ((on_face _ _).mpr corners.2.1) hx
    ((on_face _ _).mpr aL) ((on_face _ _).mpr bL) (fun h => cL ((on_face _ _).mp h))
    ((on_face _ _).mpr aR) ((on_face _ _).mpr cR) (fun h => bR ((on_face _ _).mp h)) noncollinear
  refine ⟨t, u, ht, hu, ?_⟩
  have mapped := congrArg (net.place f).linear coords
  have difference (v w : Space) : (net.place f).linear (v - w) = net.place f v - net.place f w :=
    (net.place f).linearMap_vsub v w
  simpa only [map_add, map_smul, difference] using mapped

/-- The angle in that placed cone is the full original-face angle. -/
theorem PrismFallbackDevelopment.placed_corner_angle (f : FaceLabel) (i : Fin 6)
    (member : i ∈ faceVertices f) :
    angle (net.place f (graph.prismVertex (neighbors f i).1)) (net.place f (graph.prismVertex i))
      (net.place f (graph.prismVertex (neighbors f i).2)) = graph.prismAngle small_faces f i := by
  have corners := (by decide : ∀ f i, i ∈ faceVertices f →
    (neighbors f i).1 ∈ faceVertices f ∧ (neighbors f i).2 ∈ faceVertices f) f i member
  have on_face (j : Fin 6) (h : j ∈ faceVertices f) :=
    (graph.prismVertex_mem_face small_faces prism_kind f j).mpr h
  rw [triangle_angle_of_distances _ _ _ _ _ _
    (net.rigid f _ (on_face i member) _ (on_face _ corners.1))
    (net.rigid f _ (on_face i member) _ (on_face _ corners.2))
    (net.rigid f _ (on_face _ corners.1) _ (on_face _ corners.2))]
  rw [graph.prismAngle_eq small_faces prism_kind, if_pos member]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
