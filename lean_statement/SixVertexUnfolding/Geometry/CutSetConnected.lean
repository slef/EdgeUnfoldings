import SixVertexUnfolding.Geometry.CutEndpointRetraction

/-! The cut set is path connected: it is the continuous image of the
boundary with just its source removed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Removing one point from the polyhedral sphere leaves a path-connected space. -/
theorem punctured_boundary_pathConnected (P : ConvexPolyhedron) (a : frontier P.body) :
    IsPathConnected {b : frontier P.body | b ≠ a} := by
  have connected := (P.frontier_diff_finite_pathConnected {(a : Space)} (finite_singleton _)).preimage_coe
    (show frontier P.body \ {(a : Space)} ⊆ frontier P.body from diff_subset)
  have equality : (Subtype.val : frontier P.body → Space) ⁻¹' (frontier P.body \ {(a : Space)}) =
      {b : frontier P.body | b ≠ a} := by
    ext b
    simp [Subtype.ext_iff]
  rwa [equality] at connected

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The actual cut set, including original vertices, is path connected. -/
theorem cutSet_pathConnected (a : frontier P.body) : IsPathConnected (P.cutSet a) := by
  letI : PathConnectedSpace {b : frontier P.body // b ≠ a} :=
    isPathConnected_iff_pathConnectedSpace.mp (P.punctured_boundary_pathConnected a)
  let f : {b : frontier P.body // b ≠ a} → frontier P.body :=
    fun b => (graph.cutEndpoint small_faces a b).val
  have continuous_f : Continuous f := continuous_subtype_val.comp (graph.cutEndpoint_continuous small_faces a)
  have image : f '' univ = P.cutSet a := by
    ext c
    constructor
    · rintro ⟨b, _, rfl⟩
      exact (graph.cutEndpoint small_faces a b).property
    · intro cut
      obtain ⟨b, equal⟩ := graph.cutEndpoint_surjective small_faces a ⟨c, cut⟩
      exact ⟨b, mem_univ _, congrArg Subtype.val equal⟩
  rw [← image]
  exact isPathConnected_univ.image continuous_f

include graph small_faces in
/-- The spatial trace used for the embedded graph is path connected as well. -/
theorem cutSetInSpace_pathConnected (a : frontier P.body) : IsPathConnected (P.cutSetInSpace a) :=
  (graph.cutSet_pathConnected small_faces a).image continuous_subtype_val

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
