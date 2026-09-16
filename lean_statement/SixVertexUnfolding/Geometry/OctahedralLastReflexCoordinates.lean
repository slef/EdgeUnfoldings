import SixVertexUnfolding.Geometry.OctahedralShortReflexHeight

/-! The reflected cut-edge separator is expressed directly in the actual last-flank coordinates. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem first_corner_of_last_reflex (ρ : ℝ) (reflex : (net.patch 3).rightCorner = π + ρ) :
    (net.patch 0).leftCorner = π - graph.curvature (fanNeighbor source slit) - ρ := by
  have total := net.slit_corner_sum
  rw [reflex] at total
  unfold curvature
  linarith

theorem last_reflex_bound (ρ : ℝ) (reflex : (net.patch 3).rightCorner = π + ρ) :
    ρ < π - graph.curvature (fanNeighbor source slit) := by
  have positive := (net.patch 0).leftCorner_pos
  rw [net.first_corner_of_last_reflex ρ reflex] at positive
  linarith

theorem last_apex_direction_of_reflex (ρ : ℝ) (reflex : (net.patch 3).rightCorner = π + ρ) :
    (net.patch 3).apex - (net.patch 3).right = dist (net.patch 3).apex (net.patch 3).right •
      direction (ρ - graph.curvature (opposite source)) := by
  have vector := net.patch_apex_direction_right 3
  change (net.patch 3).apex - (net.patch 3).right = _ • direction
    (graph.openingAngle (opposite source) slit 4 - π + (net.patch 3).rightCorner) at vector
  rw [graph.openingAngle_last, reflex] at vector
  have direction_eq : graph.totalAngleAt (opposite source) - π + (π + ρ) =
      (ρ - graph.curvature (opposite source)) + 2 * π := by unfold curvature; ring
  rwa [direction_eq, direction_add_two_pi] at vector

theorem first_apex_direction_of_last_reflex (ρ : ℝ) (reflex : (net.patch 3).rightCorner = π + ρ) :
    (net.patch 0).apex - (net.patch 0).left = dist (net.patch 0).apex (net.patch 0).left •
      direction (graph.curvature (fanNeighbor source slit) + ρ) := by
  rw [net.patch_apex_direction_left, net.first_corner_of_last_reflex ρ reflex]
  change _ • direction (0 + π - (π - graph.curvature (fanNeighbor source slit) - ρ)) = _
  congr 2
  ring

theorem last_petal_right_of_reflex_cut (ρ : ℝ) (reflex : (net.patch 3).rightCorner = π + ρ) :
    ∀ x ∈ net.placedTriangle (true, 3),
      det (direction (ρ - graph.curvature (opposite source))) (x - (net.patch 3).right) ≤ 0 := by
  let arm := (net.patch 3).apex - (net.patch 3).right
  have at_left : det arm ((net.patch 3).left - (net.patch 3).right) ≤ 0 := by
    have side := (net.patch 3).outward
    rw [oppositeHingeSides_iff_det _ _ _ _ (ne₁₂_of_not_collinear (net.patch 3).petal_noncollinear)] at side
    have fan := net.patch_fan_area_pos 3
    have area : det ((net.patch 3).right - (net.patch 3).left) ((net.patch 3).apex - (net.patch 3).left) ≤ 0 := by nlinarith
    have cycle : det arm ((net.patch 3).left - (net.patch 3).right) =
        det ((net.patch 3).right - (net.patch 3).left) ((net.patch 3).apex - (net.patch 3).left) := by
      simp only [arm, det, PiLp.sub_apply]
      ring
    rwa [cycle]
  let height := detHeight arm
  have inclusion : net.placedTriangle (true, 3) ⊆ {x | height x ≤ height (net.patch 3).right} := by
    rw [net.placedTriangle_hull]
    apply convexHull_min _ ((convex_Iic (height (net.patch 3).right)).linear_preimage height.toLinearMap)
    rintro x (rfl | rfl | rfl)
    · simpa only [height, detHeight_apply, det_sub_right, sub_nonpos] using at_left
    · change height (net.patch 3).right ≤ height (net.patch 3).right
      exact le_rfl
    · have zero : det arm ((net.patch 3).apex - (net.patch 3).right) = 0 := det_self arm
      simpa only [height, detHeight_apply, det_sub_right, sub_nonpos] using zero.le
  intro x member
  have side : det arm (x - (net.patch 3).right) ≤ 0 := by
    simpa only [height, detHeight_apply, det_sub_right, sub_nonpos] using inclusion member
  have length_pos : 0 < dist (net.patch 3).apex (net.patch 3).right :=
    dist_pos.mpr (ne₂₃_of_not_collinear (net.patch 3).petal_noncollinear).symm
  change det ((net.patch 3).apex - (net.patch 3).right) (x - (net.patch 3).right) ≤ 0 at side
  rw [net.last_apex_direction_of_reflex ρ reflex, det_smul_left] at side
  nlinarith

theorem last_reflex_slit_height (ρ : ℝ) (reflex : (net.patch 3).rightCorner = π + ρ)
    (crosses_gap : graph.curvature (opposite source) < ρ)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) :
    0 < det (direction (ρ - graph.curvature (opposite source))) ((net.patch 0).left - (net.patch 3).right) := by
  let κ := graph.curvature (opposite source)
  have negative := SlitSeparator.slit_height_negative net.slitRadius_pos
    (graph.curvature_pos small_faces (opposite source)) (graph.curvature_pos small_faces (fanNeighbor source slit))
    threshold crosses_gap (net.last_reflex_bound ρ reflex)
  rw [net.first_slit_position, net.last_slit_position]
  have identity : det (direction (ρ - κ)) (net.slitRadius • direction 0 - net.slitRadius • direction (-κ)) =
      -det (direction (-ρ)) (net.slitRadius • direction (-κ) - net.slitRadius • direction 0) := by
    simp only [det_sub_right, det_smul_right, direction_det]
    rw [show 0 - (ρ - κ) = -(ρ - κ) by ring, show -κ - (ρ - κ) = -ρ by ring,
      show -κ - -ρ = ρ - κ by ring, show 0 - -ρ = ρ by ring, sin_neg, sin_neg]
    ring
  change 0 < det (direction (ρ - κ)) _
  rw [identity]
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
