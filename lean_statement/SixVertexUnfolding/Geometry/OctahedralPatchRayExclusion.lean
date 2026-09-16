import SixVertexUnfolding.Geometry.OctahedralReflexLocal
import SixVertexUnfolding.Geometry.OctahedralPatchSpan
import SixVertexUnfolding.Geometry.RadialSegmentAngles

/-! A patch's strict half-fan span excludes any radial segment whose direction is far enough from one of its rays. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem zero_not_mem_petal (i : Fin 4) : (0 : Plane) ∉ net.placedTriangle (true, i) := by
  obtain ⟨height, left, right, apex⟩ := outward_patch_height (net.patch i).left (net.patch i).right
    (net.patch i).pole (net.patch i).apex (net.patch i).fan_noncollinear (net.patch i).outward
  simp only [net.patch_pole, sub_zero] at left right apex
  have inclusion : net.placedTriangle (true, i) ⊆ {x | 0 < height x} := by
    rw [net.placedTriangle_hull]
    apply convexHull_min _ ((convex_Ioi (0 : ℝ)).linear_preimage height)
    rintro x (rfl | rfl | rfl)
    exacts [left, right, apex]
  intro member
  have impossible := inclusion member
  change 0 < height 0 at impossible
  simp at impossible

theorem patch_left_mem_hull (i : Fin 4) : (net.patch i).left ∈ (net.patch i).hull :=
  net.placedTriangle_subset_patch_hull true i (net.patch_left_mem true i)

theorem patch_right_mem_hull (i : Fin 4) : (net.patch i).right ∈ (net.patch i).hull :=
  net.placedTriangle_subset_patch_hull true i (net.patch_right_mem true i)

theorem patch_left_ne_zero (i : Fin 4) : (net.patch i).left ≠ 0 :=
  fun same => net.zero_not_mem_petal i (same ▸ net.patch_left_mem true i)

theorem patch_right_ne_zero (i : Fin 4) : (net.patch i).right ≠ 0 :=
  fun same => net.zero_not_mem_petal i (same ▸ net.patch_right_mem true i)

/-- This criterion excludes closed contact, including the cut's two endpoints. -/
theorem petal_misses_radial_segment
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (i : Fin 4) (a b : Plane) (anchor : a ∈ (net.patch i).hull) (anchor_ne : a ≠ 0)
    (wide : graph.totalAngleAt (opposite source) ≤ 2 * angle a 0 b) :
    Disjoint (net.placedTriangle (true, i)) (segment ℝ 0 b) := by
  apply Set.disjoint_left.mpr
  intro x in_petal in_segment
  have x_ne : x ≠ 0 := fun same => net.zero_not_mem_petal i (same ▸ in_petal)
  have span := (net.patch i).angular_span_bound small_faces alternative a x anchor
    (net.placedTriangle_subset_patch_hull true i in_petal)
    (by rwa [net.patch_pole]) (by rwa [net.patch_pole])
  rw [net.patch_pole, angle_eq_of_mem_radial_segment a b x in_segment x_ne] at span
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
