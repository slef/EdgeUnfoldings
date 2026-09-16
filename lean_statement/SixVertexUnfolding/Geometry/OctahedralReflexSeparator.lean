import SixVertexUnfolding.Geometry.OctahedralSlitCoordinates
import SixVertexUnfolding.Geometry.PetalCutHalfplane
import SixVertexUnfolding.Geometry.SlitSeparator

/-! The actual first petal and opposite patch are strictly separated in the gap-crossing reflex case. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem first_petal_left_of_reflex_cut (ρ : ℝ) (reflex : (net.patch 0).leftCorner = π + ρ) :
    ∀ x ∈ net.placedTriangle (true, 0), 0 ≤ det (direction (-ρ)) (x - (net.patch 0).left) := by
  have arm_pos : 0 < dist (net.patch 0).apex (net.patch 0).left := by
    rw [(net.patch 0).petal_left]
    apply dist_pos.mpr
    intro same
    exact fanNeighbor_ne_source source (slit + 0) (graph.vertex.injective (Subtype.ext same)).symm
  intro x member
  have side := net.placed_petal_left_of_cut 0 x member
  rw [net.first_apex_direction_of_reflex ρ reflex, det_smul_left] at side
  nlinarith

/-- All four corners of the opposite closed patch lie strictly beyond the actual copied cut-edge line. -/
theorem opposite_patch_beyond_reflex_cut (ρ : ℝ) (reflex : (net.patch 0).leftCorner = π + ρ)
    (crosses_gap : graph.curvature (opposite source) < ρ)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) :
    ∀ x ∈ (net.patch 3).hull, det (direction (-ρ)) (x - (net.patch 0).left) < 0 := by
  have r_pos := net.slitRadius_pos
  have gap_pos := graph.curvature_pos small_faces (opposite source)
  have slit_pos := graph.curvature_pos small_faces (fanNeighbor source slit)
  have corner := net.first_reflex_bound ρ reflex
  have at_base : det (direction (-ρ)) ((net.patch 3).right - (net.patch 0).left) < 0 := by
    rw [net.last_slit_position, net.first_slit_position]
    exact SlitSeparator.slit_height_negative r_pos gap_pos slit_pos threshold crosses_gap corner
  have at_pole : det (direction (-ρ)) ((net.patch 3).pole - (net.patch 0).left) < 0 := by
    rw [net.patch_pole, net.first_slit_position]
    exact SlitSeparator.pole_height_negative r_pos gap_pos slit_pos crosses_gap corner
  have apex_ray := (SlitSeparator.opposite_directions_negative gap_pos slit_pos crosses_gap corner).2
  have at_apex : det (direction (-ρ)) ((net.patch 3).apex - (net.patch 0).left) < 0 := by
    have expression : (net.patch 3).apex - (net.patch 0).left =
        ((net.patch 3).right - (net.patch 0).left) + ((net.patch 3).apex - (net.patch 3).right) := by module
    rw [expression, det_add_right, net.last_apex_direction_of_first_reflex ρ reflex, det_smul_right]
    linarith [mul_nonpos_of_nonneg_of_nonpos (dist_nonneg : 0 ≤ dist (net.patch 3).apex (net.patch 3).right) apex_ray.le]
  have fan_corner_nonnegative := angle_nonneg (0 : Plane) (net.patch 3).right (net.patch 3).left
  have petal_corner_positive := angle_pos_of_not_collinear (net.patch 3).petal_noncollinear
  have total_corner := net.last_corner_of_first_reflex ρ reflex
  unfold DevelopedPatch.rightCorner at total_corner
  rw [net.patch_pole] at total_corner
  have base_ray : det (direction (-ρ))
      (direction (-π - graph.curvature (opposite source) + angle 0 (net.patch 3).right (net.patch 3).left)) < 0 := by
    rw [direction_det]
    apply sin_neg_of_neg_of_neg_pi_lt <;> linarith
  have at_left : det (direction (-ρ)) ((net.patch 3).left - (net.patch 0).left) < 0 := by
    have expression : (net.patch 3).left - (net.patch 0).left =
        ((net.patch 3).right - (net.patch 0).left) + ((net.patch 3).left - (net.patch 3).right) := by module
    rw [expression, det_add_right, net.last_base_direction_at_slit, det_smul_right]
    linarith [mul_nonpos_of_nonneg_of_nonpos (dist_nonneg : 0 ≤ dist (net.patch 3).left (net.patch 3).right) base_ray.le]
  let height := detHeight (direction (-ρ))
  have inclusion : (net.patch 3).hull ⊆ {x | height x < height (net.patch 0).left} := by
    apply convexHull_min _ ((convex_Iio (height (net.patch 0).left)).linear_preimage height.toLinearMap)
    rintro x (rfl | rfl | rfl | rfl)
    · simpa only [height, detHeight_apply, det_sub_right, sub_neg] using at_pole
    · simpa only [height, detHeight_apply, det_sub_right, sub_neg] using at_left
    · simpa only [height, detHeight_apply, det_sub_right, sub_neg] using at_base
    · simpa only [height, detHeight_apply, det_sub_right, sub_neg] using at_apex
  intro x member
  simpa only [height, detHeight_apply, det_sub_right, sub_neg] using inclusion member

/-- The separator now applies to the actual net, including both endpoints of the opposite finite cut. -/
theorem first_reflex_closed_separation (ρ : ℝ) (reflex : (net.patch 0).leftCorner = π + ρ)
    (crosses_gap : graph.curvature (opposite source) < ρ)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) :
    Disjoint (net.placedTriangle (true, 0)) (net.patch 3).hull ∧
      Disjoint (net.placedTriangle (true, 0)) (segment ℝ 0 (net.patch 3).right) := by
  have left := net.first_petal_left_of_reflex_cut ρ reflex
  constructor
  · apply Set.disjoint_left.mpr
    intro x hx other
    exact (not_lt_of_ge (left x hx)) (net.opposite_patch_beyond_reflex_cut ρ reflex crosses_gap threshold x other)
  · apply Set.disjoint_left.mpr
    intro x hx other
    have negative := SlitSeparator.finite_slit_height_negative net.slitRadius_pos
      (graph.curvature_pos small_faces (opposite source))
      (graph.curvature_pos small_faces (fanNeighbor source slit)) threshold crosses_gap
      (net.first_reflex_bound ρ reflex) (by rwa [net.last_slit_position] at other)
    rw [← net.first_slit_position] at negative
    exact (not_lt_of_ge (left x hx)) negative

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
