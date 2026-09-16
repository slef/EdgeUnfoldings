import SixVertexUnfolding.Geometry.OctahedralReflexSeparator
import SixVertexUnfolding.Geometry.OctahedralPatchAngleBounds
import SixVertexUnfolding.OctahedronCore

/-! All three local pairs are proved for the first-flank gap-crossing reflex branch. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem last_petal_below_slit_line (ρ : ℝ) (reflex : (net.patch 0).leftCorner = π + ρ)
    (crosses_gap : graph.curvature (opposite source) < ρ) :
    ∀ x ∈ net.placedTriangle (true, 3), det (direction (-graph.curvature (opposite source))) x ≤ 0 := by
  let d := direction (-graph.curvature (opposite source))
  have gap_pos := graph.curvature_pos small_faces (opposite source)
  have slit_pos := graph.curvature_pos small_faces (fanNeighbor source slit)
  have corner := net.first_reflex_bound ρ reflex
  have at_base : det d (net.patch 3).right = 0 := by
    rw [net.last_slit_position, det_smul_right]
    change net.slitRadius * det d d = 0
    rw [det_self, mul_zero]
  have at_left : det d (net.patch 3).left ≤ 0 := by
    have expression : (net.patch 3).left = (net.patch 3).right + ((net.patch 3).left - (net.patch 3).right) := by module
    rw [expression, det_add_right, at_base, zero_add, net.last_base_direction_at_slit, det_smul_right]
    apply mul_nonpos_of_nonneg_of_nonpos dist_nonneg
    rw [direction_det]
    apply sin_nonpos_of_nonpos_of_neg_pi_le <;>
      linarith [angle_nonneg (0 : Plane) (net.patch 3).right (net.patch 3).left,
        angle_le_pi (0 : Plane) (net.patch 3).right (net.patch 3).left]
  have at_apex : det d (net.patch 3).apex ≤ 0 := by
    have expression : (net.patch 3).apex = (net.patch 3).right + ((net.patch 3).apex - (net.patch 3).right) := by module
    rw [expression, det_add_right, at_base, zero_add, net.last_apex_direction_of_first_reflex ρ reflex, det_smul_right]
    apply mul_nonpos_of_nonneg_of_nonpos dist_nonneg
    rw [direction_det]
    exact (sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)).le
  let height := detHeight d
  change net.placedTriangle (true, 3) ⊆ {x | height x ≤ 0}
  rw [net.placedTriangle_hull]
  apply convexHull_min _ ((convex_Iic (0 : ℝ)).linear_preimage height.toLinearMap)
  rintro x (rfl | rfl | rfl)
  · exact at_left
  · exact at_base.le
  · exact at_apex

theorem first_fan_above_last_slit_line (ρ : ℝ) (reflex : (net.patch 0).leftCorner = π + ρ)
    (crosses_gap : graph.curvature (opposite source) < ρ) :
    ∀ x ∈ net.placedTriangle (false, 0), 0 ≤ det (direction (-graph.curvature (opposite source))) x := by
  let d := direction (-graph.curvature (opposite source))
  have gap_pos := graph.curvature_pos small_faces (opposite source)
  have slit_pos := graph.curvature_pos small_faces (fanNeighbor source slit)
  have corner := net.first_reflex_bound ρ reflex
  have width := net.first_reflex_fan_width ρ reflex
  have at_left : 0 ≤ det d (net.patch 0).left := by
    rw [net.first_slit_position, det_smul_right, direction_det]
    apply mul_nonneg net.slitRadius_pos.le
    apply sin_nonneg_of_nonneg_of_le_pi <;> linarith
  have at_right : 0 ≤ det d (net.patch 0).right := by
    rw [net.patch_right]
    change 0 ≤ det d (_ • direction (graph.openingAngle (opposite source) slit 1))
    rw [det_smul_right, direction_det]
    apply mul_nonneg dist_nonneg
    apply sin_nonneg_of_nonneg_of_le_pi
    · linarith [graph.openingAngle_nonneg (opposite source) slit 1]
    · linarith
  have at_pole : 0 ≤ det d (net.patch 0).pole := by rw [net.patch_pole]; simp [det]
  let height := detHeight d
  change net.placedTriangle (false, 0) ⊆ {x | 0 ≤ height x}
  rw [net.placedTriangle_hull]
  apply convexHull_min _ ((convex_Ici (0 : ℝ)).linear_preimage height.toLinearMap)
  rintro x (rfl | rfl | rfl)
  · exact at_left
  · exact at_right
  · exact at_pole

theorem last_petal_first_fan_of_first_reflex (ρ : ℝ) (reflex : (net.patch 0).leftCorner = π + ρ)
    (crosses_gap : graph.curvature (opposite source) < ρ) : net.Separated (true, 3) (false, 0) := by
  apply disjoint_interiors_of_halfplanes (detHeight (direction (-graph.curvature (opposite source))))
    (direction_height_surjective _) 0
  · exact net.last_petal_below_slit_line ρ reflex crosses_gap
  · exact net.first_fan_above_last_slit_line ρ reflex crosses_gap

theorem placedTriangle_subset_patch_hull (petal : Bool) (i : Fin 4) :
    net.placedTriangle (petal, i) ⊆ (net.patch i).hull := by
  rw [net.placedTriangle_hull, DevelopedPatch.hull]
  apply convexHull_mono
  intro x member
  cases petal <;> simp only [Bool.false_eq_true, if_false, if_true, Set.mem_insert_iff, Set.mem_singleton_iff] at member ⊢ <;> tauto

/-- In this branch, both the slit-edge separator and the final radial separator use the same actual net. -/
theorem first_reflex_local_pairs (ρ : ℝ) (reflex : (net.patch 0).leftCorner = π + ρ)
    (crosses_gap : graph.curvature (opposite source) < ρ)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) : net.LocalPairs := by
  have separated := (net.first_reflex_closed_separation ρ reflex crosses_gap threshold).1
  have safe (petal : Bool) : net.Separated (true, 0) (petal, 3) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp separated (interior_subset hx)
      (net.placedTriangle_subset_patch_hull petal 3 (interior_subset hy))
  exact ⟨safe true, safe false, net.last_petal_first_fan_of_first_reflex ρ reflex crosses_gap⟩

/-- A readable branch condition without an auxiliary reflex-angle parameter. -/
theorem local_pairs_of_first_corner_crosses_gap
    (crosses_gap : π + graph.curvature (opposite source) < (net.patch 0).leftCorner)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) : net.LocalPairs := by
  apply net.first_reflex_local_pairs ((net.patch 0).leftCorner - π) (by ring) (by linarith) threshold

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
