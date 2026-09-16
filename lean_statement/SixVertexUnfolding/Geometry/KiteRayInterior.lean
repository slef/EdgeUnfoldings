import SixVertexUnfolding.Geometry.PlacedTriangleGeometry
import SixVertexUnfolding.Geometry.TriangleFanInterior
import SixVertexUnfolding.Geometry.JoinedTriangleInterior

/-! A positive point of a ray ending in an open cut-tree edge lies
inside the paired kite, including when it is on the common base. -/

namespace SixVertexUnfolding.ConvexPolyhedron.PlacedCutEdgeTriangles

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (D : PlacedCutEdgeTriangles T edge)

theorem open_base_interior :
    openSegment ℝ (D.motion D.model.left) (D.motion D.model.right) ⊆ interior D.kite := by
  have opposite := bisector_sites_opposite (D.motion D.model.first) (D.motion D.model.second)
    (D.motion D.model.left) (D.motion D.model.right) (D.motion.injective.ne D.model.distinct_sources)
    (D.motion.injective.ne D.model.base_different)
    (by simpa only [D.motion.dist_map] using D.model.left_distances)
    (by simpa only [D.motion.dist_map] using D.model.right_distances)
  have interior := open_base_in_joined_triangles_of_opposite (D.motion D.model.left)
    (D.motion D.model.right) (D.motion D.model.first) (D.motion D.model.second) opposite
  have rotate (p l r : Plane) : ({l, r, p} : Set Plane) = {p, l, r} := by
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  rw [rotate (D.motion D.model.first) (D.motion D.model.left) (D.motion D.model.right),
    rotate (D.motion D.model.second) (D.motion D.model.left) (D.motion D.model.right)] at interior
  exact interior

theorem interior_ray_in_kite (side : Bool) (s t : unitInterval)
    (base_positive : 0 < s) (base_before : s < 1) (time_positive : 0 < t) :
    triangleFanMap (D.motion (D.apex side)) (D.motion D.model.left) (D.motion D.model.right) (s, t) ∈ interior D.kite := by
  rcases t.property.2.eq_or_lt with last | before
  · have last : t = 1 := Subtype.ext last
    subst t
    apply D.open_base_interior
    change AffineMap.lineMap _ (AffineMap.lineMap _ _ (s : ℝ)) 1 ∈ _
    rw [AffineMap.lineMap_apply_one, openSegment_eq_image_lineMap]
    exact ⟨s, ⟨base_positive, base_before⟩, rfl⟩
  · apply interior_mono (D.side_subset_kite side)
    exact (triangleFan_interior_iff _ _ _ (D.side_noncollinear side) (s, t)).mpr
      ⟨base_positive, base_before, time_positive, before⟩

end SixVertexUnfolding.ConvexPolyhedron.PlacedCutEdgeTriangles
