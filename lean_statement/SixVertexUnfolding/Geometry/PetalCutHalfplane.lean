import SixVertexUnfolding.Geometry.HingeDeterminant
import SixVertexUnfolding.Geometry.OctahedralPlacedTopology

/-! The oriented copied cut edge bounds a closed half-plane containing its entire petal. -/

namespace SixVertexUnfolding

open Real

theorem radial_triangle_base_area (r s α β : ℝ) :
    det (s • direction β - r • direction α) (0 - r • direction α) = r * s * sin (β - α) := by
  simp only [det, PiLp.sub_apply, PiLp.zero_apply, PiLp.smul_apply, direction_x, direction_y, smul_eq_mul, sin_sub]
  ring

theorem petal_cut_halfplane (a b w p : Plane) (base_ne : a ≠ b)
    (fan_area : 0 < det (b - a) (w - a)) (outward : OppositeHingeSides a b w p) :
    ∀ x ∈ convexHull ℝ ({a, b, p} : Set Plane), 0 ≤ det (p - a) (x - a) := by
  rw [oppositeHingeSides_iff_det a b w p base_ne] at outward
  have area_nonpositive : det (b - a) (p - a) ≤ 0 := by
    by_contra positive
    have impossible := mul_pos fan_area (lt_of_not_ge positive)
    linarith
  have at_b : 0 ≤ det (p - a) (b - a) := by rw [det_swap]; linarith
  let height := detHeight (p - a)
  have inclusion : convexHull ℝ ({a, b, p} : Set Plane) ⊆ {x | height a ≤ height x} := by
    apply convexHull_min _ ((convex_Ici (height a)).linear_preimage height.toLinearMap)
    intro x member
    change height a ≤ height x
    rcases member with same | same | same
    · rw [same]
    · rw [same]
      simpa only [height, detHeight_apply, det_sub_right, sub_nonneg] using at_b
    · change x = p at same
      rw [same]
      have zero : det (p - a) (p - a) = 0 := det_self _
      simpa only [height, detHeight_apply, det_sub_right, sub_nonneg] using zero.ge
  intro x member
  simpa only [height, detHeight_apply, det_sub_right, sub_nonneg] using inclusion member

namespace ConvexPolyhedron.SixVertexGraph.Development

open OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem patch_fan_area_pos (i : Fin 4) :
    0 < det ((net.patch i).right - (net.patch i).left) ((net.patch i).pole - (net.patch i).left) := by
  rw [net.patch_pole, net.patch_right, net.patch_left]
  change 0 < det (_ • direction _ - _ • direction _) (0 - _ • direction _)
  rw [radial_triangle_base_area, graph.openingAngle_step]
  exact mul_pos (mul_pos (graph.opening_radius_pos _ _ _) (graph.opening_radius_pos _ _ _))
    (sin_pos_of_pos_of_lt_pi (graph.fanAngle_pos _ _) (graph.fanAngle_lt_pi _ _))

theorem placed_petal_left_of_cut (i : Fin 4) : ∀ x ∈ net.placedTriangle (true, i),
    0 ≤ det ((net.patch i).apex - (net.patch i).left) (x - (net.patch i).left) := by
  rw [net.placedTriangle_hull]
  apply petal_cut_halfplane _ _ (net.patch i).pole _ _ (net.patch_fan_area_pos i) (net.patch i).outward
  intro same
  have positive := net.patch_fan_area_pos i
  rw [same, sub_self] at positive
  simp [det] at positive

end ConvexPolyhedron.SixVertexGraph.Development
end SixVertexUnfolding
