import SixVertexUnfolding.Geometry.EdgeTerminalRecovery

/-! Source recovery is continuous near curves visiting the two-face metric
neighborhood. Its finite candidate list isolates the recovered source. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set BoundedContinuousFunction
open scoped Topology

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G)

/-- Joined-source recovery is continuous at curves whose two evaluation points stay in a two-face neighborhood. -/
theorem recoveredSource_continuousAt (t : unitInterval) (f : P.BoundaryCurve)
    (U : Set Space) (openU : IsOpen U) (covers : U ∩ frontier P.body ⊆ F.val ∪ G.val)
    (inside : (f t : Space) ∈ U) (target : (f 1 : Space) ∈ U) :
    ContinuousAt (chart.recoveredSource t) f := by
  have evaluation (u : unitInterval) : Continuous (fun g : P.BoundaryCurve => (g u : Space)) :=
    continuous_subtype_val.comp (continuous_eval_const u)
  have joined (u : unitInterval) (fu : (f u : Space) ∈ U) :
      ContinuousAt (fun g : P.BoundaryCurve => chart.unfold (g u)) f := by
    have on : ContinuousOn (fun g : P.BoundaryCurve => chart.unfold (g u))
        ((fun g : P.BoundaryCurve => (g u : Space)) ⁻¹' U) :=
      chart.unfold_continuousOn.comp (evaluation u).continuousOn (fun g hg => covers ⟨hg, (g u).property⟩)
    exact on.continuousAt ((openU.preimage (evaluation u)).mem_nhds fu)
  exact continuousAt_const.smul ((joined t inside).sub (continuousAt_const.smul (joined 1 target)))

/-- Nearby recovered sources cannot move between members of the finite joined source list. -/
theorem recoveredSource_isolation (a : Space) (t : unitInterval) (f : P.BoundaryCurve)
    (U : Set Space) (openU : IsOpen U) (covers : U ∩ frontier P.body ⊆ F.val ∪ G.val)
    (inside : (f t : Space) ∈ U) (target : (f 1 : Space) ∈ U) :
    ∃ W : Set P.BoundaryCurve, IsOpen W ∧ f ∈ W ∧ ∀ g ∈ W,
      chart.recoveredSource t g ∈ chart.sourceImages a → chart.recoveredSource t g = chart.recoveredSource t f := by
  let other := chart.sourceImages a \ {chart.recoveredSource t f}
  have open_complement : IsOpen otherᶜ := (chart.sourceImages_finite a).diff.isClosed.isOpen_compl
  have near := (chart.recoveredSource_continuousAt t f U openU covers inside target).eventually
    (open_complement.mem_nhds (fun h => h.2 rfl))
  obtain ⟨W, subset, openW, fW⟩ := mem_nhds_iff.mp near
  refine ⟨W, openW, fW, ?_⟩
  intro g gW member
  by_contra different
  exact subset gW ⟨member, different⟩

/-- Each recovered source of an actual nearby canonical route belongs to that finite list. -/
theorem recoveredSource_mem (graph : P.SixVertexGraph)
    (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (H.val ∩ (P.vertices : Set Space)).ncard = 4)
    (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves) (different : f 0 ≠ f 1)
    (U : Set Space) (openU : IsOpen U) (targetU : (f 1 : Space) ∈ U)
    (only_two : ∀ H : P.Face, (f 1 : Space) ∈ H.val → H = F ∨ H = G)
    (metric : ∀ x ∈ U ∩ frontier P.body, ∀ y ∈ U ∩ frontier P.body,
      P.surfaceDist x y = dist (chart.unfold x) (chart.unfold y))
    (t : unitInterval) (before : t < 1) (inside : (f t : Space) ∈ U) :
    chart.recoveredSource t f ∈ chart.sourceImages (f 0) := by
  obtain ⟨source, member, terminal⟩ := chart.exists_terminal_source graph small_faces f geodesic different only_two
  rw [chart.recoveredSource_of_terminal f geodesic source terminal U openU targetU metric t before inside]
  exact member

/-- Equal recovered sources and endpoints give equal earlier positions in the joined development. -/
theorem recoveredSource_position (t : unitInterval) (before : t < 1) (f g : P.BoundaryCurve)
    (same : chart.recoveredSource t f = chart.recoveredSource t g) (target : f 1 = g 1) :
    chart.unfold (f t) = chart.unfold (g t) := by
  have nonzero : (1 - (t : ℝ))⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt (sub_pos.mpr (show (t : ℝ) < 1 from before)))
  change _ • _ = _ • _ at same
  have equal := (smul_right_injective (M := Plane) nonzero) same
  rw [target] at equal
  exact add_right_cancel (by simpa only [sub_eq_add_neg] using equal)

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
