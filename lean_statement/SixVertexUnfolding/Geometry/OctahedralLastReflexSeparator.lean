import SixVertexUnfolding.Geometry.OctahedralLastReflexCoordinates

/-! The last-flank crossing case uses its own actual cut edge as the strict separator. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem first_patch_beyond_last_reflex_cut (ρ : ℝ) (reflex : (net.patch 3).rightCorner = π + ρ)
    (crosses_gap : graph.curvature (opposite source) < ρ)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) :
    ∀ x ∈ (net.patch 0).hull,
      0 < det (direction (ρ - graph.curvature (opposite source))) (x - (net.patch 3).right) := by
  let d := direction (ρ - graph.curvature (opposite source))
  have gap_pos := graph.curvature_pos small_faces (opposite source)
  have slit_pos := graph.curvature_pos small_faces (fanNeighbor source slit)
  have corner := net.last_reflex_bound ρ reflex
  have at_base : 0 < det d ((net.patch 0).left - (net.patch 3).right) := net.last_reflex_slit_height ρ reflex crosses_gap threshold
  have at_pole : 0 < det d ((net.patch 0).pole - (net.patch 3).right) := by
    rw [net.patch_pole, net.last_slit_position]
    change 0 < det (direction (ρ - graph.curvature (opposite source))) (0 - net.slitRadius • direction (-graph.curvature (opposite source)))
    rw [det_sub_right, det_smul_right, direction_det]
    have zero : det (direction (ρ - graph.curvature (opposite source))) (0 : Plane) = 0 := by simp [det]
    rw [zero, show -graph.curvature (opposite source) - (ρ - graph.curvature (opposite source)) = -ρ by ring, sin_neg]
    have positive := mul_pos net.slitRadius_pos (sin_pos_of_pos_of_lt_pi (by linarith : 0 < ρ) (by linarith : ρ < π))
    nlinarith
  have apex_ray : 0 < det d (direction (graph.curvature (fanNeighbor source slit) + ρ)) := by
    rw [direction_det]
    apply sin_pos_of_pos_of_lt_pi <;> linarith
  have at_apex : 0 < det d ((net.patch 0).apex - (net.patch 3).right) := by
    have expression : (net.patch 0).apex - (net.patch 3).right =
        ((net.patch 0).left - (net.patch 3).right) + ((net.patch 0).apex - (net.patch 0).left) := by module
    rw [expression, det_add_right, net.first_apex_direction_of_last_reflex ρ reflex, det_smul_right]
    linarith [mul_nonneg (dist_nonneg : 0 ≤ dist (net.patch 0).apex (net.patch 0).left) apex_ray.le]
  have fan_nonnegative := angle_nonneg (0 : Plane) (net.patch 0).left (net.patch 0).right
  have petal_nonnegative := angle_nonneg (net.patch 0).right (net.patch 0).left (net.patch 0).apex
  have first_corner := net.first_corner_of_last_reflex ρ reflex
  unfold DevelopedPatch.leftCorner at first_corner
  rw [net.patch_pole] at first_corner
  have base_ray : 0 < det d (direction (π - angle 0 (net.patch 0).left (net.patch 0).right)) := by
    rw [direction_det]
    apply sin_pos_of_pos_of_lt_pi <;> linarith
  have at_right : 0 < det d ((net.patch 0).right - (net.patch 3).right) := by
    have vector := net.patch_base_direction_left 0
    change (net.patch 0).right - (net.patch 0).left = _ • direction
      (0 + π - angle 0 (net.patch 0).left (net.patch 0).right) at vector
    rw [zero_add] at vector
    have expression : (net.patch 0).right - (net.patch 3).right =
        ((net.patch 0).left - (net.patch 3).right) + ((net.patch 0).right - (net.patch 0).left) := by module
    rw [expression, det_add_right, vector, det_smul_right]
    linarith [mul_nonneg (dist_nonneg : 0 ≤ dist (net.patch 0).left (net.patch 0).right) base_ray.le]
  let height := detHeight d
  have inclusion : (net.patch 0).hull ⊆ {x | height (net.patch 3).right < height x} := by
    apply convexHull_min _ ((convex_Ioi (height (net.patch 3).right)).linear_preimage height.toLinearMap)
    rintro x (rfl | rfl | rfl | rfl)
    · simpa only [height, detHeight_apply, det_sub_right, sub_pos] using at_pole
    · simpa only [height, detHeight_apply, det_sub_right, sub_pos] using at_base
    · simpa only [height, detHeight_apply, det_sub_right, sub_pos] using at_right
    · simpa only [height, detHeight_apply, det_sub_right, sub_pos] using at_apex
  intro x member
  simpa only [height, detHeight_apply, det_sub_right, sub_pos] using inclusion member

theorem last_reflex_closed_separation (ρ : ℝ) (reflex : (net.patch 3).rightCorner = π + ρ)
    (crosses_gap : graph.curvature (opposite source) < ρ)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) :
    Disjoint (net.placedTriangle (true, 3)) (net.patch 0).hull ∧
      Disjoint (net.placedTriangle (true, 3)) (segment ℝ 0 (net.patch 0).left) := by
  have right := net.last_petal_right_of_reflex_cut ρ reflex
  have positive := net.first_patch_beyond_last_reflex_cut ρ reflex crosses_gap threshold
  have separated : Disjoint (net.placedTriangle (true, 3)) (net.patch 0).hull := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge (right x hx)) (positive x hy)
  refine ⟨separated, separated.mono_right ?_⟩
  apply (convex_convexHull ℝ _).segment_subset
  · change (0 : Plane) ∈ convexHull ℝ _
    apply subset_convexHull ℝ _
    rw [net.patch_pole]
    simp
  · exact net.patch_left_mem_hull 0

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
