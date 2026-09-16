import SixVertexUnfolding.Geometry.OctahedralPocketFaceAvoidance
import SixVertexUnfolding.Geometry.PocketComponent

/-! The protected patch triangles stay in the closures of their own pocket-complement components. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- Any interior seed determines a complement component whose closure contains the whole first triangle. -/
theorem first_patch_in_closure_component
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (p : Plane) (left : p ∈ net.placedTriangle (true, 1)) (right : p ∈ net.placedTriangle (true, 3))
    (petal : Bool) (seed : Plane) (inside : seed ∈ interior (net.placedTriangle (petal, 0))) :
    net.placedTriangle (petal, 0) ⊆ closure (connectedComponentIn
      (segment ℝ (net.patch 1).left p ∪ segment ℝ p (net.patch 3).right ∪
        segment ℝ 0 (net.patch 3).right ∪ segment ℝ 0 (net.patch 1).left)ᶜ seed) :=
  convex_face_in_closure_component _ _ (net.placedTriangle_convex _) (net.placedTriangle_regular _)
    (net.last_pocket_boundary_avoids_first_patch source_order maximal p left right petal) seed inside

/-- The same component containment holds for either triangle of the reflected last patch. -/
theorem last_patch_in_closure_component
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (p : Plane) (left : p ∈ net.placedTriangle (true, 0)) (right : p ∈ net.placedTriangle (true, 2))
    (petal : Bool) (seed : Plane) (inside : seed ∈ interior (net.placedTriangle (petal, 3))) :
    net.placedTriangle (petal, 3) ⊆ closure (connectedComponentIn
      (segment ℝ (net.patch 0).left p ∪ segment ℝ p (net.patch 2).right ∪
        segment ℝ 0 (net.patch 2).right ∪ segment ℝ 0 (net.patch 0).left)ᶜ seed) :=
  convex_face_in_closure_component _ _ (net.placedTriangle_convex _) (net.placedTriangle_regular _)
    (net.first_pocket_boundary_avoids_last_patch source_order maximal p left right petal) seed inside

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
