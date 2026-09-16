import SixVertexUnfolding.Geometry.SurfaceReparameterization

/-! Paths with fixed endpoints, on the closed boundary, and with a common
speed bound form a compact family. Length is lower semicontinuous there. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter BoundedContinuousFunction
open scoped ENNReal NNReal Topology

/-- The auxiliary compact family used to obtain a shortest surface route. -/
def boundedSpeedCurves (P : ConvexPolyhedron) (a b : Space) (C : ℝ≥0) :
    Set (unitInterval →ᵇ Space) :=
  {f | f 0 = a ∧ f 1 = b ∧ (∀ t, f t ∈ frontier P.body) ∧ LipschitzWith C f}

/-- Fixed endpoints, a closed surface, and a speed bound survive uniform limits. -/
theorem boundedSpeedCurves_closed (P : ConvexPolyhedron) (a b : Space) (C : ℝ≥0) :
    IsClosed (P.boundedSpeedCurves a b C) := by
  have evaluation (t : unitInterval) : Continuous (fun f : unitInterval →ᵇ Space => f t) :=
    continuous_eval_const t
  have speeds : IsClosed {f : unitInterval →ᵇ Space | LipschitzWith C f} := by
    simp only [LipschitzWith, setOf_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun y =>
      isClosed_le ((evaluation x).edist (evaluation y)) continuous_const))
  unfold boundedSpeedCurves
  simp only [setOf_and, setOf_forall]
  exact (isClosed_eq (evaluation 0) continuous_const).inter
    ((isClosed_eq (evaluation 1) continuous_const).inter
      ((isClosed_iInter (fun t => isClosed_frontier.preimage (evaluation t))).inter
        speeds))

/-- Arzelà–Ascoli applies because the boundary is compact and all speeds share one bound. -/
theorem boundedSpeedCurves_compact (P : ConvexPolyhedron) (a b : Space) (C : ℝ≥0) :
    IsCompact (P.boundedSpeedCurves a b C) := by
  apply BoundedContinuousFunction.arzela_ascoli₂ (frontier P.body)
    (P.body_compact.of_isClosed_subset isClosed_frontier P.body_compact.isClosed.frontier_subset)
    _ (P.boundedSpeedCurves_closed a b C) (fun f t hf => hf.2.2.1 t)
  apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => C * r)
    (by simpa using (tendsto_const_nhds.mul (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0))))
  intro x y f
  exact f.property.2.2.2.dist_le_mul x y

/-- A uniform limit cannot have more length than the limiting lower bound of the lengths. -/
theorem curve_length_lowerSemicontinuous :
    LowerSemicontinuous (fun f : unitInterval →ᵇ Space => eVariationOn f Set.univ) := by
  intro f length smaller
  exact eVariationOn.lowerSemicontinuous_aux
    (fun t _ => (continuous_eval_const t).tendsto f) smaller

/-- The compact family has a length minimizer whenever it contains at least one path. -/
theorem boundedSpeedCurves_minimum (P : ConvexPolyhedron) (a b : Space) (C : ℝ≥0)
    (nonempty : (P.boundedSpeedCurves a b C).Nonempty) :
    ∃ f ∈ P.boundedSpeedCurves a b C,
      ∀ g ∈ P.boundedSpeedCurves a b C,
        eVariationOn f Set.univ ≤ eVariationOn g Set.univ :=
  (curve_length_lowerSemicontinuous.lowerSemicontinuousOn _).exists_isMinOn nonempty
    (P.boundedSpeedCurves_compact a b C)

end SixVertexUnfolding.ConvexPolyhedron
