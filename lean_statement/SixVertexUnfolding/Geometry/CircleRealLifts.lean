import SixVertexUnfolding.Definitions

/-! A map from a contractible space to the circle has a continuous real
lift. One full turn increases that lift by one; a constant circle path does not. -/

namespace SixVertexUnfolding

open Set

/-- Contractibility removes every obstruction to lifting a circle-valued map to the real line. -/
theorem circle_map_real_lift {X : Type*} [TopologicalSpace X] [ContractibleSpace X]
    (f : C(X, AddCircle (1 : ℝ))) : ∃ g : C(X, ℝ), ∀ x, (g x : AddCircle (1 : ℝ)) = f x := by
  obtain ⟨center, ⟨contraction⟩⟩ := id_nullhomotopic X
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (f center)
  let H := (ContinuousMap.Homotopy.refl f).comp contraction.symm
  let initial : C(X, ℝ) := ContinuousMap.const X r
  have at_zero : ∀ x, H (0, x) = (initial x : AddCircle (1 : ℝ)) := by
    intro x
    rw [H.apply_zero]
    exact hr.symm
  let lift := (AddCircle.isCoveringMap_coe (1 : ℝ)).liftHomotopy H.toContinuousMap initial at_zero
  refine ⟨lift.comp ((ContinuousMap.const X (1 : unitInterval)).prodMk (ContinuousMap.id X)), ?_⟩
  intro x
  have lifted := congrFun ((AddCircle.isCoveringMap_coe (1 : ℝ)).liftHomotopy_lifts
    H.toContinuousMap initial at_zero) (1, x)
  exact lifted.trans (H.apply_one x)

/-- A lift of one positively oriented turn has endpoint difference one. -/
theorem real_lift_one_turn (g : C(unitInterval, ℝ))
    (projects : ∀ t, (g t : AddCircle (1 : ℝ)) = ((t : ℝ) : AddCircle (1 : ℝ))) :
    g 1 = g 0 + 1 := by
  have constant := (AddCircle.isCoveringMap_coe (1 : ℝ)).const_of_comp
    (g.continuous.sub continuous_subtype_val)
    (fun s t => by simp only [AddCircle.coe_sub, projects, sub_self]) (1 : unitInterval) 0
  change g 1 - (1 : ℝ) = g 0 - (0 : ℝ) at constant
  linarith

/-- Along an edge mapped constantly to the circle, every real lift is constant. -/
theorem real_lift_constant_circle (g : C(unitInterval, ℝ))
    (projects : ∀ t, (g t : AddCircle (1 : ℝ)) = 0) : g 0 = g 1 :=
  (AddCircle.isCoveringMap_coe (1 : ℝ)).const_of_comp g.continuous
    (fun s t => (projects s).trans (projects t).symm) 0 1

end SixVertexUnfolding
