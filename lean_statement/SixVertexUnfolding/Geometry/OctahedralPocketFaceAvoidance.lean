import SixVertexUnfolding.Geometry.OctahedralPocketCandidate

/-! The candidate pocket boundary cannot cross the interiors of the patch that the pocket must contain. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- Both triangles of the first patch avoid every closed side of the last-triple pocket. -/
theorem last_pocket_boundary_avoids_first_patch
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (p : Plane) (left : p ∈ net.placedTriangle (true, 1)) (right : p ∈ net.placedTriangle (true, 3))
    (petal : Bool) :
    Disjoint (interior (net.placedTriangle (petal, 0)))
      (segment ℝ (net.patch 1).left p ∪ segment ℝ p (net.patch 3).right ∪
        segment ℝ 0 (net.patch 3).right ∪ segment ℝ 0 (net.patch 1).left) := by
  have local_pairs := net.selected_local_pairs source_order maximal
  have safe : net.Separated (petal, 0) (true, 1) ∧ net.Separated (petal, 0) (true, 3) ∧
      net.Separated (petal, 0) (false, 3) ∧ net.Separated (petal, 0) (false, 1) := by
    cases petal
    · exact ⟨net.neighboring_fan_petal 0, local_pairs.right.symm,
        net.fan.nonoverlap 0 3 (by decide), net.fan.nonoverlap 0 1 (by decide)⟩
    · exact ⟨net.neighboring_petals 0, local_pairs.petals, local_pairs.left, net.neighboring_petal_fan 0⟩
  apply Set.disjoint_left.mpr
  intro x inside on_boundary
  rcases on_boundary with ((on_left | on_right) | on_last_ray) | on_first_ray
  · exact Set.disjoint_left.mp safe.1.interior_disjoint_closed inside
      ((net.placedTriangle_convex (true, 1)).segment_subset (net.patch_left_mem true 1) left on_left)
  · exact Set.disjoint_left.mp safe.2.1.interior_disjoint_closed inside
      ((net.placedTriangle_convex (true, 3)).segment_subset right (net.patch_right_mem true 3) on_right)
  · exact Set.disjoint_left.mp safe.2.2.1.interior_disjoint_closed inside
      ((net.placedTriangle_convex (false, 3)).segment_subset (net.fan_pole_mem 3) (net.patch_right_mem false 3) on_last_ray)
  · exact Set.disjoint_left.mp safe.2.2.2.interior_disjoint_closed inside
      ((net.placedTriangle_convex (false, 1)).segment_subset (net.fan_pole_mem 1) (net.patch_left_mem false 1) on_first_ray)

/-- The last patch is likewise protected from the reflected first-triple boundary. -/
theorem first_pocket_boundary_avoids_last_patch
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (p : Plane) (left : p ∈ net.placedTriangle (true, 0)) (right : p ∈ net.placedTriangle (true, 2))
    (petal : Bool) :
    Disjoint (interior (net.placedTriangle (petal, 3)))
      (segment ℝ (net.patch 0).left p ∪ segment ℝ p (net.patch 2).right ∪
        segment ℝ 0 (net.patch 2).right ∪ segment ℝ 0 (net.patch 0).left) := by
  have local_pairs := net.selected_local_pairs source_order maximal
  have safe : net.Separated (petal, 3) (true, 0) ∧ net.Separated (petal, 3) (true, 2) ∧
      net.Separated (petal, 3) (false, 2) ∧ net.Separated (petal, 3) (false, 0) := by
    cases petal
    · exact ⟨local_pairs.left.symm, (net.neighboring_petal_fan 2).symm,
        net.fan.nonoverlap 3 2 (by decide), net.fan.nonoverlap 3 0 (by decide)⟩
    · exact ⟨local_pairs.petals.symm, (net.neighboring_petals 2).symm,
        (net.neighboring_fan_petal 2).symm, local_pairs.right⟩
  apply Set.disjoint_left.mpr
  intro x inside on_boundary
  rcases on_boundary with ((on_left | on_right) | on_last_ray) | on_first_ray
  · exact Set.disjoint_left.mp safe.1.interior_disjoint_closed inside
      ((net.placedTriangle_convex (true, 0)).segment_subset (net.patch_left_mem true 0) left on_left)
  · exact Set.disjoint_left.mp safe.2.1.interior_disjoint_closed inside
      ((net.placedTriangle_convex (true, 2)).segment_subset right (net.patch_right_mem true 2) on_right)
  · exact Set.disjoint_left.mp safe.2.2.1.interior_disjoint_closed inside
      ((net.placedTriangle_convex (false, 2)).segment_subset (net.fan_pole_mem 2) (net.patch_right_mem false 2) on_last_ray)
  · exact Set.disjoint_left.mp safe.2.2.2.interior_disjoint_closed inside
      ((net.placedTriangle_convex (false, 0)).segment_subset (net.fan_pole_mem 0) (net.patch_left_mem false 0) on_first_ray)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
