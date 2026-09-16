import SixVertexUnfolding.Definitions
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Rigid coordinate changes on a tree can be put in one common plane.
Frames are propagated along the unique path from a fixed root, so they
are chosen once for the whole tree, not separately for each comparison. -/

namespace SixVertexUnfolding

namespace TreeFrames

variable {V : Type*} (G : SimpleGraph V)
    (motion : ∀ {u v : V}, G.Adj u v → Plane ≃ᵃⁱ[ℝ] Plane)

/-- Compose the local coordinate changes along an oriented walk. -/
noncomputable def along : ∀ {u v : V}, G.Walk u v → Plane ≃ᵃⁱ[ℝ] Plane
  | _, _, .nil => AffineIsometryEquiv.refl ℝ Plane
  | _, _, .cons edge tail => (motion edge).trans (along tail)

theorem along_concat {u v w : V} (path : G.Walk u v) (edge : G.Adj v w) :
    along G motion (path.concat edge) = (along G motion path).trans (motion edge) := by
  induction path with
  | nil => rfl
  | cons first tail ih =>
    simp only [SimpleGraph.Walk.concat_cons, along, ih]
    rfl

/-- Inverse-compatible changes on the edges of a tree admit global frames. -/
theorem exists_common_frames (tree : G.IsTree)
    (reverse : ∀ {u v : V} (edge : G.Adj u v), motion edge.symm = (motion edge).symm)
    (root : V) :
    ∃ frame : V → Plane ≃ᵃⁱ[ℝ] Plane,
      frame root = AffineIsometryEquiv.refl ℝ Plane ∧
      ∀ {u v : V} (edge : G.Adj u v) (x : Plane), frame v (motion edge x) = frame u x := by
  classical
  let path (v : V) := (tree.existsUnique_path root v).choose
  have simple (v : V) : (path v).IsPath := (tree.existsUnique_path root v).choose_spec.1
  let frame (v : V) := (along G motion (path v)).symm
  have root_path : path root = SimpleGraph.Walk.nil :=
    (tree.existsUnique_path root root).unique (simple root) SimpleGraph.Walk.IsPath.nil
  refine ⟨frame, ?_, ?_⟩
  · change (along G motion (path root)).symm = _
    rw [root_path]
    rfl
  · intro u v edge x
    by_cases before : u ∈ (path v).support
    · have extended := tree.isAcyclic.path_concat (simple u) (simple v) edge before
      change (along G motion (path v)).symm (motion edge x) = (along G motion (path u)).symm x
      rw [extended, along_concat]
      change (along G motion (path u)).symm ((motion edge).symm (motion edge x)) = _
      rw [(motion edge).symm_apply_apply]
    · have other_before := tree.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
        (simple u) (simple v) edge before
      have extended := tree.isAcyclic.path_concat (simple v) (simple u) edge.symm other_before
      change (along G motion (path v)).symm (motion edge x) = (along G motion (path u)).symm x
      rw [extended, along_concat, reverse edge]
      rfl

end TreeFrames
end SixVertexUnfolding
