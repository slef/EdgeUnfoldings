import SixVertexUnfolding.Geometry.TreeFrames

/-! Choose one admissible change of coordinates per unoriented edge.
The reverse change is its inverse, so the tree-frame theorem applies. -/

namespace SixVertexUnfolding.TreeFrames

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- An inverse-stable geometric condition can be met coherently in both edge directions. -/
theorem choose_inverse_transitions
    (good : ∀ {u v : V}, G.Adj u v → (Plane ≃ᵃⁱ[ℝ] Plane) → Prop)
    (exists_good : ∀ {u v : V} (edge : G.Adj u v), ∃ motion, good edge motion)
    (inverse_good : ∀ {u v : V} (edge : G.Adj u v) motion,
      good edge motion → good edge.symm motion.symm) :
    ∃ motion : ∀ {u v : V}, G.Adj u v → Plane ≃ᵃⁱ[ℝ] Plane,
      (∀ {u v : V} (edge : G.Adj u v), good edge (motion edge)) ∧
      ∀ {u v : V} (edge : G.Adj u v), motion edge.symm = (motion edge).symm := by
  classical
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  let chosen {u v : V} (edge : G.Adj u v) := (exists_good edge).choose
  have chosen_good {u v : V} (edge : G.Adj u v) : good edge (chosen edge) :=
    (exists_good edge).choose_spec
  let motion {u v : V} (edge : G.Adj u v) :=
    if u < v then chosen edge else (chosen edge.symm).symm
  refine ⟨@motion, ?_, ?_⟩
  · intro u v edge
    by_cases order : u < v
    · simpa only [motion, if_pos order] using chosen_good edge
    · simpa only [motion, if_neg order] using inverse_good edge.symm (chosen edge.symm) (chosen_good edge.symm)
  · intro u v edge
    by_cases order : u < v
    · simp only [motion, if_pos order, if_neg (not_lt_of_ge order.le)]
    · have other : v < u := lt_of_le_of_ne (le_of_not_gt order) edge.ne.symm
      simp only [motion, if_neg order, if_pos other, AffineIsometryEquiv.symm_symm]

/-- Select geometric transitions and put all local charts in one common frame. -/
theorem exists_frames_for_transitions (tree : G.IsTree) (root : V)
    (good : ∀ {u v : V}, G.Adj u v → (Plane ≃ᵃⁱ[ℝ] Plane) → Prop)
    (exists_good : ∀ {u v : V} (edge : G.Adj u v), ∃ motion, good edge motion)
    (inverse_good : ∀ {u v : V} (edge : G.Adj u v) motion,
      good edge motion → good edge.symm motion.symm) :
    ∃ motion : ∀ {u v : V}, G.Adj u v → Plane ≃ᵃⁱ[ℝ] Plane,
      ∃ frame : V → Plane ≃ᵃⁱ[ℝ] Plane,
        (∀ {u v : V} (edge : G.Adj u v), good edge (motion edge)) ∧
        frame root = AffineIsometryEquiv.refl ℝ Plane ∧
        ∀ {u v : V} (edge : G.Adj u v) (x : Plane), frame v (motion edge x) = frame u x := by
  obtain ⟨motion, valid, reverse⟩ := choose_inverse_transitions G good exists_good inverse_good
  obtain ⟨frame, at_root, compatible⟩ := exists_common_frames G motion tree reverse root
  exact ⟨motion, frame, valid, at_root, compatible⟩

end SixVertexUnfolding.TreeFrames
