import SixVertexUnfolding.Geometry.OctahedralPatch

/-! The strict half-fan bound holds on the entire closed developed patch. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.DevelopedPatch

open EuclideanGeometry Real

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph} {source : Fin 6} {sector : Fin 4}
variable (patch : graph.DevelopedPatch source sector)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- Any two non-pole points of the whole patch subtend strictly less than half the fan's angle sum.
This includes every boundary point and the convex hull of a reflex patch. -/
theorem angular_span_bound
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (OctahedralTriangles.opposite source) ≤ π)
    (x y : Plane) (hx : x ∈ patch.hull) (hy : y ∈ patch.hull)
    (x_ne : x ≠ patch.pole) (y_ne : y ≠ patch.pole) :
    2 * angle x patch.pole y < graph.totalAngleAt (OctahedralTriangles.opposite source) := by
  let ray : Fin 3 → Plane := ![patch.left - patch.pole, patch.right - patch.pole, patch.apex - patch.pole]
  obtain ⟨height, left_pos, right_pos, apex_pos⟩ := outward_patch_height
    patch.left patch.right patch.pole patch.apex patch.fan_noncollinear patch.outward
  have positive (i : Fin 3) : 0 < height (ray i) := by
    fin_cases i
    exacts [left_pos, right_pos, apex_pos]
  have ray_ne (i : Fin 3) : ray i ≠ 0 := by
    intro zero
    have strict := positive i
    simp [zero] at strict
  obtain ⟨fan, left, right⟩ := patch.corner_angle_bounds small_faces alternative
  change 2 * InnerProductGeometry.angle (ray 0) (ray 1) < _ at fan
  change 2 * InnerProductGeometry.angle (ray 0) (ray 2) < _ at left
  change 2 * InnerProductGeometry.angle (ray 1) (ray 2) < _ at right
  have corners (i j : Fin 3) : InnerProductGeometry.angle (ray i) (ray j) <
      graph.totalAngleAt (OctahedralTriangles.opposite source) / 2 := by
    have total_positive := graph.totalAngleAt_pos (OctahedralTriangles.opposite source)
    fin_cases i <;> fin_cases j
    · change InnerProductGeometry.angle (ray 0) (ray 0) < _
      rw [InnerProductGeometry.angle_self (ray_ne 0)]
      linarith
    · change InnerProductGeometry.angle (ray 0) (ray 1) < _
      linarith
    · change InnerProductGeometry.angle (ray 0) (ray 2) < _
      linarith
    · change InnerProductGeometry.angle (ray 1) (ray 0) < _
      rw [InnerProductGeometry.angle_comm]
      linarith
    · change InnerProductGeometry.angle (ray 1) (ray 1) < _
      rw [InnerProductGeometry.angle_self (ray_ne 1)]
      linarith
    · change InnerProductGeometry.angle (ray 1) (ray 2) < _
      linarith
    · change InnerProductGeometry.angle (ray 2) (ray 0) < _
      rw [InnerProductGeometry.angle_comm]
      linarith
    · change InnerProductGeometry.angle (ray 2) (ray 1) < _
      rw [InnerProductGeometry.angle_comm]
      linarith
    · change InnerProductGeometry.angle (ray 2) (ray 2) < _
      rw [InnerProductGeometry.angle_self (ray_ne 2)]
      linarith
  have shifted (z : Plane) (member : z ∈ patch.hull) :
      z - patch.pole ∈ convexHull ℝ (insert 0 (Set.range ray)) := by
    let shift : Plane →ᵃ[ℝ] Plane := (AffineEquiv.vaddConst ℝ (-patch.pole)).toAffineMap
    have image_member : shift z ∈ shift '' patch.hull := Set.mem_image_of_mem shift member
    rw [hull, shift.image_convexHull] at image_member
    have vertices : shift '' ({patch.pole, patch.left, patch.right, patch.apex} : Set Plane) =
        insert 0 (Set.range ray) := by
      ext p
      simp [shift, ray, Set.image_insert_eq, Set.image_singleton, sub_eq_add_neg]
      tauto
    rw [vertices] at image_member
    exact image_member
  have bound := zero_triangle_hull_angular_bound height ray _ positive corners
    (x - patch.pole) (y - patch.pole) (shifted x hx) (shifted y hy)
    (sub_ne_zero.mpr x_ne) (sub_ne_zero.mpr y_ne)
  change angle x patch.pole y < _ at bound
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.DevelopedPatch
