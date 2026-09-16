import SixVertexUnfolding.Geometry.OctahedralLastReflexSeparator
import SixVertexUnfolding.Geometry.OctahedralShortReflexLocal

/-! The complete local slit lemma for the actual selected development. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem last_fan_below_first_slit_of_reflex (ρ : ℝ) (reflex : (net.patch 3).rightCorner = π + ρ)
    (crosses_gap : graph.curvature (opposite source) < ρ) :
    ∀ x ∈ net.placedTriangle (false, 3), det (direction 0) x ≤ 0 := by
  have gap_pos := graph.curvature_pos small_faces (opposite source)
  have slit_pos := graph.curvature_pos small_faces (fanNeighbor source slit)
  have corner := net.last_reflex_bound ρ reflex
  have width := net.last_reflex_fan_width ρ reflex
  have gap_total : graph.totalAngleAt (opposite source) + graph.curvature (opposite source) = 2 * π := by unfold curvature; ring
  have at_right : det (direction 0) (net.patch 3).right ≤ 0 := by
    rw [net.last_slit_position, det_smul_right, direction_det, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos net.slitRadius_pos.le
      (sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)).le
  have at_left : det (direction 0) (net.patch 3).left ≤ 0 := by
    rw [net.patch_left]
    change det (direction 0) (_ • direction (graph.openingAngle (opposite source) slit 3)) ≤ 0
    rw [det_smul_right, direction_det, sub_zero]
    apply mul_nonpos_of_nonneg_of_nonpos dist_nonneg
    have shifted := sin_neg_of_neg_of_neg_pi_lt
      (show graph.openingAngle (opposite source) slit 3 - 2 * π < 0 by
        linarith [graph.openingAngle_le_total (opposite source) slit 3])
      (show -π < graph.openingAngle (opposite source) slit 3 - 2 * π by linarith)
    rw [sin_sub_two_pi] at shifted
    exact shifted.le
  let height := detHeight (direction 0)
  change net.placedTriangle (false, 3) ⊆ {x | height x ≤ 0}
  rw [net.placedTriangle_hull]
  apply convexHull_min _ ((convex_Iic (0 : ℝ)).linear_preimage height.toLinearMap)
  rintro x (rfl | rfl | rfl)
  · exact at_left
  · exact at_right
  · rw [net.patch_pole]; simp [height, det]

theorem last_reflex_local_pairs (ρ : ℝ) (reflex : (net.patch 3).rightCorner = π + ρ)
    (crosses_gap : graph.curvature (opposite source) < ρ)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) : net.LocalPairs := by
  have separated := (net.last_reflex_closed_separation ρ reflex crosses_gap threshold).1
  have safe (petal : Bool) : net.Separated (true, 3) (petal, 0) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp separated (interior_subset hx)
      (net.placedTriangle_subset_patch_hull petal 0 (interior_subset hy))
  refine ⟨(safe true).symm, ?_, safe false⟩
  apply Disjoint.symm
  apply disjoint_interiors_of_halfplanes (detHeight (direction 0)) (direction_height_surjective 0) 0
  · exact net.last_fan_below_first_slit_of_reflex ρ reflex crosses_gap
  · have first_corner := net.first_corner_of_last_reflex ρ reflex
    have gap_pos := graph.curvature_pos small_faces (opposite source)
    have slit_pos := graph.curvature_pos small_faces (fanNeighbor source slit)
    intro x member
    exact net.first_patch_inward (by linarith) x (net.placedTriangle_subset_patch_hull true 0 member)

/-- All three local pairs are safe under the half-fan alternative and the closed slit-curvature threshold. -/
theorem local_pairs
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) : net.LocalPairs := by
  by_cases last_corner : (net.patch 3).rightCorner ≤ π + graph.curvature (opposite source)
  · exact net.local_pairs_unless_last_corner_crosses_gap alternative threshold last_corner
  · exact net.last_reflex_local_pairs ((net.patch 3).rightCorner - π) (by ring) (by linarith) threshold

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
