import SixVertexUnfolding.Geometry.Edges

/-! Planar motions aligning the two endpoints of an original hinge. -/

namespace SixVertexUnfolding

/-- Equal-length ordered segments are related by a planar rigid motion. -/
theorem exists_plane_motion (a b c d : Plane) (same_length : dist a b = dist c d) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, motion a = c ∧ motion b = d := by
  let turn := (Submodule.span ℝ {((b - a) - (d - c))}).orthogonal.reflection
  have equal_norms : ‖b - a‖ = ‖d - c‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using same_length
  have turn_direction : turn (b - a) = d - c := Submodule.reflection_sub equal_norms
  let motion := ((AffineIsometryEquiv.vaddConst ℝ a).symm.trans
    turn.toAffineIsometryEquiv).trans (AffineIsometryEquiv.vaddConst ℝ c)
  have formula (x : Plane) : motion x = turn (x - a) + c := rfl
  refine ⟨motion, ?_, ?_⟩
  · rw [formula, sub_self, map_zero, zero_add]
  · rw [formula, turn_direction, sub_add_cancel]

namespace ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F G : P.Face)

/-- A rigid motion can align two rigid face placements along their entire common edge. -/
theorem exists_hinge_motion (edge : P.ShareEdge F G)
    (left right : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (left x) (left y) = dist x y)
    (right_rigid : ∀ x ∈ G.val, ∀ y ∈ G.val, dist (right x) (right y) = dist x y) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane,
      ∀ x ∈ F.val ∩ G.val, motion (right x) = left x := by
  obtain ⟨a, _, b, _, _, endpoints⟩ := F.shared_edge_endpoints G edge
  have a_shared : a ∈ F.val ∩ G.val := by rw [endpoints]; exact left_mem_segment ℝ a b
  have b_shared : b ∈ F.val ∩ G.val := by rw [endpoints]; exact right_mem_segment ℝ a b
  obtain ⟨motion, at_a, at_b⟩ := exists_plane_motion (right a) (right b) (left a) (left b)
    ((right_rigid a a_shared.2 b b_shared.2).trans
      (left_rigid a a_shared.1 b b_shared.1).symm)
  refine ⟨motion, ?_⟩
  have agree : Set.EqOn (motion.toAffineEquiv.toAffineMap.comp right) left {a, b} := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact at_a
    · rw [Set.mem_singleton_iff.mp hx]
      exact at_b
  intro x hx
  rw [endpoints, ← convexHull_pair] at hx
  exact AffineMap.eqOn_affineSpan agree (convexHull_subset_affineSpan _ hx)

end ConvexPolyhedron.Face
end SixVertexUnfolding
