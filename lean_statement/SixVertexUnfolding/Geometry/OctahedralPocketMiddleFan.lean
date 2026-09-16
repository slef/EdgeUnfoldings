import SixVertexUnfolding.Geometry.OctahedralPocketComponents

/-! The middle fan face cannot cross the candidate pocket boundary either. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- This supplies the protected middle face used to determine the pocket's sector at the pole. -/
theorem pocket_boundary_avoids_middle_fan (i : Fin 2) (p : Plane)
    (left : p ∈ net.placedTriangle (true, i.castSucc.castSucc))
    (right : p ∈ net.placedTriangle (true, i.succ.succ)) :
    Disjoint (interior (net.placedTriangle (false, i.castSucc.succ)))
      (segment ℝ (net.patch i.castSucc.castSucc).left p ∪ segment ℝ p (net.patch i.succ.succ).right ∪
        segment ℝ 0 (net.patch i.succ.succ).right ∪ segment ℝ 0 (net.patch i.castSucc.castSucc).left) := by
  have left_safe : net.Separated (false, i.castSucc.succ) (true, i.castSucc.castSucc) :=
    (net.neighboring_petal_fan i.castSucc).symm
  have right_safe : net.Separated (false, i.castSucc.succ) (true, i.succ.succ) :=
    net.neighboring_fan_petal i.succ
  have next_safe : net.Separated (false, i.castSucc.succ) (false, i.succ.succ) :=
    net.fan.nonoverlap _ _ (by intro same; have values := congrArg Fin.val same; simp at values)
  have previous_safe : net.Separated (false, i.castSucc.succ) (false, i.castSucc.castSucc) :=
    net.fan.nonoverlap _ _ (by intro same; have values := congrArg Fin.val same; simp at values)
  apply Set.disjoint_left.mpr
  intro x inside on_boundary
  rcases on_boundary with ((on_left | on_right) | on_next_ray) | on_previous_ray
  · exact Set.disjoint_left.mp left_safe.interior_disjoint_closed inside
      ((net.placedTriangle_convex _).segment_subset (net.patch_left_mem true _) left on_left)
  · exact Set.disjoint_left.mp right_safe.interior_disjoint_closed inside
      ((net.placedTriangle_convex _).segment_subset right (net.patch_right_mem true _) on_right)
  · exact Set.disjoint_left.mp next_safe.interior_disjoint_closed inside
      ((net.placedTriangle_convex _).segment_subset (net.fan_pole_mem _) (net.patch_right_mem false _) on_next_ray)
  · exact Set.disjoint_left.mp previous_safe.interior_disjoint_closed inside
      ((net.placedTriangle_convex _).segment_subset (net.fan_pole_mem _) (net.patch_left_mem false _) on_previous_ray)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
