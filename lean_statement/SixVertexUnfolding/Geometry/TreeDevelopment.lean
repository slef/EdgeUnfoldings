import SixVertexUnfolding.Geometry.FacePlacement
import SixVertexUnfolding.Geometry.HingePlacement

/-!
Rigidly develop all facets along a chosen tree of original hinges. The unique
path from a root gives a consistent placement for each face. This construction
establishes rigidity and hinge agreement; it makes no nonoverlap claim.
-/

namespace SixVertexUnfolding

namespace TreeDevelopment

variable {P : ConvexPolyhedron} {hinges : SimpleGraph P.Face}

/-- Compose hinge motions along a walk, carrying its final face into its initial coordinates. -/
noncomputable def walkMotion
    (transition : ∀ F G, hinges.Adj F G → Plane ≃ᵃⁱ[ℝ] Plane) :
    {F G : P.Face} → hinges.Walk F G → Plane ≃ᵃⁱ[ℝ] Plane
  | _, _, .nil => AffineIsometryEquiv.refl ℝ Plane
  | _, _, .cons adjacent tail => (walkMotion transition tail).trans (transition _ _ adjacent)

theorem walkMotion_concat
    (transition : ∀ F G, hinges.Adj F G → Plane ≃ᵃⁱ[ℝ] Plane)
    {F G H : P.Face} (path : hinges.Walk F G) (adjacent : hinges.Adj G H) :
    walkMotion transition (path.concat adjacent) =
      (transition G H adjacent).trans (walkMotion transition path) := by
  induction path with
  | nil => simp [SimpleGraph.Walk.concat_nil, walkMotion]
  | cons head tail induction_hypothesis =>
    simp only [SimpleGraph.Walk.concat_cons, walkMotion, induction_hypothesis,
      AffineIsometryEquiv.trans_assoc]

end TreeDevelopment

/-- Every tree of original face hinges admits a simultaneous rigid planar development.
Overlaps are allowed in this intermediate result. -/
theorem exists_tree_development (P : ConvexPolyhedron) (hinges : SimpleGraph P.Face)
    (tree : hinges.IsTree) (original_edges : hinges ≤ P.dualGraph) :
    ∃ place : P.Face → Space →ᵃ[ℝ] Plane,
      (∀ F, ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place F x) (place F y) = dist x y) ∧
      (∀ F G, hinges.Adj F G → ∀ x ∈ F.val ∩ G.val, place F x = place G x) := by
  classical
  -- First place every face independently, then choose a motion across each hinge.
  choose canonical canonical_rigid using fun F : P.Face => F.exists_rigid_placement
  have hinge_motions : ∀ F G, hinges.Adj F G →
      ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane,
        ∀ x ∈ F.val ∩ G.val, motion (canonical G x) = canonical F x := by
    intro F G adjacent
    exact F.exists_hinge_motion G (original_edges adjacent) (canonical F) (canonical G)
      (canonical_rigid F) (canonical_rigid G)
  choose transition transition_joins using hinge_motions

  -- Transport each face along its unique path from the root.
  let root : P.Face := Classical.choice tree.connected.nonempty
  choose path path_isPath _ using tree.existsUnique_path root
  let place : P.Face → Space →ᵃ[ℝ] Plane := fun F =>
    (TreeDevelopment.walkMotion transition (path F)).toAffineEquiv.toAffineMap.comp (canonical F)
  refine ⟨place, ?_, ?_⟩
  · intro F x hx y hy
    change dist ((TreeDevelopment.walkMotion transition (path F)) (canonical F x))
      ((TreeDevelopment.walkMotion transition (path F)) (canonical F y)) = dist x y
    rw [AffineIsometryEquiv.dist_map]
    exact canonical_rigid F x hx y hy
  · have join_forward {F G : P.Face} (adjacent : hinges.Adj F G)
        (path_extension : path G = (path F).concat adjacent) :
        ∀ x ∈ F.val ∩ G.val, place F x = place G x := by
      intro x hx
      change (TreeDevelopment.walkMotion transition (path F)) (canonical F x) =
        (TreeDevelopment.walkMotion transition (path G)) (canonical G x)
      rw [path_extension, TreeDevelopment.walkMotion_concat]
      change (TreeDevelopment.walkMotion transition (path F)) (canonical F x) =
        (TreeDevelopment.walkMotion transition (path F)) (transition F G adjacent (canonical G x))
      rw [transition_joins F G adjacent x hx]
    intro F G adjacent x hx
    by_cases forward : F ∈ (path G).support
    · exact join_forward adjacent
        (tree.isAcyclic.path_concat (path_isPath F) (path_isPath G) adjacent forward) x hx
    · have backward := tree.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
        (path_isPath F) (path_isPath G) adjacent forward
      exact (join_forward adjacent.symm
        (tree.isAcyclic.path_concat (path_isPath G) (path_isPath F) adjacent.symm backward)
        x ⟨hx.2, hx.1⟩).symm

end SixVertexUnfolding
