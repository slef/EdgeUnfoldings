import SixVertexUnfolding.Geometry.OctahedralTriangleFrame
import SixVertexUnfolding.Geometry.TriangleCones

/-! Containment of the entire actual petals in the two apex cones, in one common rigid frame. -/

namespace SixVertexUnfolding

theorem det_triangle_cyclic (a b c : Plane) : det (a - c) (b - c) = det (b - a) (c - a) := by
  simp only [det, PiLp.sub_apply]
  ring

namespace ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem placed_petal_image (i : Fin 4) (motion : Plane ≃ᵃⁱ[ℝ] Plane) :
    motion '' net.placedTriangle (true, i) = convexHull ℝ
      ({motion (net.patch i).left, motion (net.patch i).right, motion (net.patch i).apex} : Set Plane) := by
  rw [net.placedTriangle_hull]
  change motion.toAffineMap '' convexHull ℝ _ = _
  rw [motion.toAffineMap.image_convexHull]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

/-- The left opposite petal turns clockwise from its shared source edge in the upper middle frame. -/
theorem petal_image_in_clockwise_cone (i : Fin 4) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (reverses : ∀ x y : Plane, det (motion.linearIsometryEquiv x) (motion.linearIsometryEquiv y) = -det x y)
    (r α β : ℝ) (r_pos : 0 < r)
    (edge : motion (net.patch i).right - motion (net.patch i).apex = r • direction β)
    (wide_enough : angle (net.patch i).right (net.patch i).apex (net.patch i).left ≤ β - α)
    (width_small : β - α < π) :
    motion '' net.placedTriangle (true, i) ⊆ translatedCone (motion (net.patch i).apex) (direction α) (direction β) := by
  have displacement (p q : Plane) : motion p - motion q = motion.linearIsometryEquiv (p - q) :=
    (motion.map_vsub p q).symm
  have measured := motion.toAffineIsometry.angle_map (net.patch i).right (net.patch i).apex (net.patch i).left
  change angle (motion (net.patch i).right) (motion (net.patch i).apex) (motion (net.patch i).left) = _ at measured
  have noncollinear : ¬ Collinear ℝ ({(net.patch i).right, (net.patch i).apex, (net.patch i).left} : Set Plane) := by
    have reorder : ({(net.patch i).right, (net.patch i).apex, (net.patch i).left} : Set Plane) =
        {(net.patch i).left, (net.patch i).right, (net.patch i).apex} := by ext x; simp; tauto
    rw [reorder]
    exact (net.patch i).petal_noncollinear
  rw [net.placed_petal_image, Set.insert_comm]
  apply clockwise_triangle_in_cone _ _ _ r α β r_pos
  · rw [motion.dist_map]
    exact dist_pos.mpr (ne₂₃_of_not_collinear noncollinear)
  · rw [measured]; exact angle_pos_of_not_collinear noncollinear
  · rw [measured]; exact angle_lt_pi_of_not_collinear noncollinear
  · exact edge
  · rw [displacement, displacement, reverses, det_swap, neg_neg, det_triangle_cyclic]
    exact (net.patch_petal_area_neg i).le
  · rw [measured]; exact wide_enough
  · exact width_small

/-- The right opposite petal turns counterclockwise from its shared source edge. -/
theorem petal_image_in_counterclockwise_cone (i : Fin 4) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (reverses : ∀ x y : Plane, det (motion.linearIsometryEquiv x) (motion.linearIsometryEquiv y) = -det x y)
    (r α β : ℝ) (r_pos : 0 < r)
    (edge : motion (net.patch i).left - motion (net.patch i).apex = r • direction α)
    (wide_enough : angle (net.patch i).left (net.patch i).apex (net.patch i).right ≤ β - α)
    (width_small : β - α < π) :
    motion '' net.placedTriangle (true, i) ⊆ translatedCone (motion (net.patch i).apex) (direction α) (direction β) := by
  have displacement (p q : Plane) : motion p - motion q = motion.linearIsometryEquiv (p - q) :=
    (motion.map_vsub p q).symm
  have measured := motion.toAffineIsometry.angle_map (net.patch i).left (net.patch i).apex (net.patch i).right
  change angle (motion (net.patch i).left) (motion (net.patch i).apex) (motion (net.patch i).right) = _ at measured
  have noncollinear : ¬ Collinear ℝ ({(net.patch i).left, (net.patch i).apex, (net.patch i).right} : Set Plane) := by
    rw [Set.pair_comm]
    exact (net.patch i).petal_noncollinear
  rw [net.placed_petal_image]
  apply counterclockwise_triangle_in_cone _ _ _ r α β r_pos
  · rw [motion.dist_map]
    exact dist_pos.mpr (ne₂₃_of_not_collinear noncollinear)
  · rw [measured]; exact angle_pos_of_not_collinear noncollinear
  · rw [measured]; exact angle_lt_pi_of_not_collinear noncollinear
  · exact edge
  · rw [displacement, displacement, reverses, det_triangle_cyclic]
    exact neg_nonneg.mpr (net.patch_petal_area_neg i).le
  · rw [measured]; exact wide_enough
  · exact width_small

end ConvexPolyhedron.SixVertexGraph.Development
end SixVertexUnfolding
