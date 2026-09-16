import SixVertexUnfolding.Geometry.OctahedralPocketBoundary
import SixVertexUnfolding.Geometry.FiniteLineAvoidance
import SixVertexUnfolding.Geometry.QuadrilateralBoundary

/-! An actual overlap supplies a four-sided pocket boundary with all six side-pair intersections checked. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The generic point can avoid additional lines needed by later pocket-containment arguments. -/
theorem exists_last_pocket_boundary
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (overlap : ¬ net.Separated (true, 1) (true, 3)) (extra_lines : Finset (Plane × Plane)) :
    ∃ p, p ∈ interior (net.placedTriangle (true, 1)) ∧ p ∈ interior (net.placedTriangle (true, 3)) ∧
      QuadrilateralBoundary (net.patch 1).left p (net.patch 3).right 0 ∧
      ∀ endpoints ∈ extra_lines, p ∉ affineSpan ℝ ({endpoints.1, endpoints.2} : Set Plane) := by
  classical
  let a := (net.patch 1).left
  let b := (net.patch 3).right
  let lines := extra_lines ∪ ({(a, b), (a, 0), (b, 0)} : Finset (Plane × Plane))
  have nonempty : (interior (net.placedTriangle (true, 1)) ∩ interior (net.placedTriangle (true, 3))).Nonempty :=
    Set.not_disjoint_iff_nonempty_inter.mp overlap
  obtain ⟨p, inside, avoids⟩ := exists_point_avoiding_lines lines _
    (isOpen_interior.inter isOpen_interior) nonempty
  have sides := net.last_pocket_nonadjacent_sides source_order maximal p inside.1 inside.2
  have radial : ∀ x ∈ segment ℝ 0 a, x ∈ segment ℝ 0 b → x = 0 := by
    intro x first last
    apply net.opposite_fan_pair_meet_only_at_zero 1 x
    · exact (net.placedTriangle_convex (false, 1)).segment_subset
        (net.fan_pole_mem 1) (net.patch_left_mem false 1) first
    · exact (net.placedTriangle_convex (false, 3)).segment_subset
        (net.fan_pole_mem 3) (net.patch_right_mem false 3) last
  refine ⟨p, inside.1, inside.2, ?_, fun endpoints h => avoids endpoints (Finset.mem_union_left _ h)⟩
  exact quadrilateralBoundary_of_off_lines a p b 0 sides.1 sides.2 radial
    (avoids (a, b) (by simp [lines])) (avoids (a, 0) (by simp [lines]))
    (avoids (b, 0) (by simp [lines]))

/-- The first-triple construction has the same explicit boundary certificate. -/
theorem exists_first_pocket_boundary
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (overlap : ¬ net.Separated (true, 0) (true, 2)) (extra_lines : Finset (Plane × Plane)) :
    ∃ p, p ∈ interior (net.placedTriangle (true, 0)) ∧ p ∈ interior (net.placedTriangle (true, 2)) ∧
      QuadrilateralBoundary (net.patch 0).left p (net.patch 2).right 0 ∧
      ∀ endpoints ∈ extra_lines, p ∉ affineSpan ℝ ({endpoints.1, endpoints.2} : Set Plane) := by
  classical
  let a := (net.patch 0).left
  let b := (net.patch 2).right
  let lines := extra_lines ∪ ({(a, b), (a, 0), (b, 0)} : Finset (Plane × Plane))
  have nonempty : (interior (net.placedTriangle (true, 0)) ∩ interior (net.placedTriangle (true, 2))).Nonempty :=
    Set.not_disjoint_iff_nonempty_inter.mp overlap
  obtain ⟨p, inside, avoids⟩ := exists_point_avoiding_lines lines _
    (isOpen_interior.inter isOpen_interior) nonempty
  have sides := net.first_pocket_nonadjacent_sides source_order maximal p inside.1 inside.2
  have radial : ∀ x ∈ segment ℝ 0 a, x ∈ segment ℝ 0 b → x = 0 := by
    intro x first last
    apply net.opposite_fan_pair_meet_only_at_zero 0 x
    · exact (net.placedTriangle_convex (false, 0)).segment_subset
        (net.fan_pole_mem 0) (net.patch_left_mem false 0) first
    · exact (net.placedTriangle_convex (false, 2)).segment_subset
        (net.fan_pole_mem 2) (net.patch_right_mem false 2) last
  refine ⟨p, inside.1, inside.2, ?_, fun endpoints h => avoids endpoints (Finset.mem_union_left _ h)⟩
  exact quadrilateralBoundary_of_off_lines a p b 0 sides.2 sides.1 radial
    (avoids (a, b) (by simp [lines])) (avoids (a, 0) (by simp [lines]))
    (avoids (b, 0) (by simp [lines]))

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
