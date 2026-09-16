import SixVertexUnfolding.Geometry.EdgeSourceDistance
import SixVertexUnfolding.Geometry.EdgeSourceStability

/-! Near an actual route ending in a metric edge patch, the terminal source
is fixed. A unique route therefore gives one local source-distance formula. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch

open Set BoundedContinuousFunction

variable {P : ConvexPolyhedron} {center z : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} {chart : EdgeFolding facets F G} (patch : chart.MetricPatch z)
  (graph : P.SixVertexGraph)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Nearby shortest routes from the same source have the same actual terminal source in the joined chart. -/
theorem geodesic_branch_source (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (target : (f 1 : Space) ∈ patch.domain) :
    ∃ source ∈ chart.sourceImages (f 0), chart.HasTerminalSource f source ∧
      ∃ W : Set P.BoundaryCurve, IsOpen W ∧ f ∈ W ∧
      ∀ g ∈ W, g ∈ P.geodesicCurves → g 0 = f 0 →
        chart.HasTerminalSource g source ∧ P.surfaceDist (g 0) (g 1) = dist source (chart.unfold (g 1)) := by
  let path := P.surfacePathOfCurve f
  obtain ⟨t, _, before, ftU, _⟩ := path.common_time_near_target path patch.domain patch.open_domain target
  obtain ⟨V, openV, fV, isolated⟩ := chart.recoveredSource_isolation (f 0) t f
    patch.domain patch.open_domain patch.on_facets ftU target
  have evaluation (u : unitInterval) : Continuous (fun g : P.BoundaryCurve => (g u : Space)) :=
    continuous_subtype_val.comp (continuous_eval_const u)
  let W : Set P.BoundaryCurve := (fun g => (g t : Space)) ⁻¹' patch.domain ∩
    ((fun g => (g 1 : Space)) ⁻¹' patch.domain ∩ ({g | g 0 ≠ g 1} ∩ V))
  have openW : IsOpen W := (patch.open_domain.preimage (evaluation t)).inter
    ((patch.open_domain.preimage (evaluation 1)).inter
      ((isClosed_eq (continuous_eval_const 0) (continuous_eval_const 1)).isOpen_compl.inter openV))
  obtain ⟨source, member, terminal⟩ := chart.exists_terminal_source graph small_faces f geodesic different (patch.only_two _ target)
  have original := chart.recoveredSource_of_terminal f geodesic source terminal
    patch.domain patch.open_domain target patch.metric t before ftU
  refine ⟨source, member, terminal, W, openW, ⟨ftU, target, different, fV⟩, ?_⟩
  intro g near shortest same_start
  obtain ⟨other, member_g, terminal_g⟩ := chart.exists_terminal_source graph small_faces g shortest near.2.2.1
    (patch.only_two _ near.2.1)
  have recovered := chart.recoveredSource_of_terminal g shortest other terminal_g
    patch.domain patch.open_domain near.2.1 patch.metric t before near.1
  have candidate : chart.recoveredSource t g ∈ chart.sourceImages (f 0) := by
    rw [recovered, ← same_start]
    exact member_g
  have same : other = source := recovered.symm.trans ((isolated g near.2.2.2 candidate).trans original)
  rw [same] at terminal_g
  exact ⟨terminal_g, chart.terminal_source_distance patch g shortest source terminal_g near.2.1⟩

include graph small_faces in
/-- A unique route to any point in this edge patch has one local distance formula in the same joined coordinates. -/
theorem unique_route_source_distance (a b : frontier P.body) (different : a ≠ b)
    (target : (b : Space) ∈ patch.domain) (unique : (P.geodesicFiber a b).Subsingleton) :
    ∃ source ∈ chart.sourceImages a, ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧
      ∀ x ∈ V ∩ frontier P.body, P.surfaceDist a x = dist source (chart.unfold x) := by
  obtain ⟨f, hf⟩ := P.geodesicFiber_nonempty a b
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  obtain ⟨source, member, _, W, openW, fW, formula⟩ := patch.geodesic_branch_source graph small_faces f hf.1
    (by simpa only [first, last] using different) (by simpa only [last] using target)
  obtain ⟨N, openN, abN, contains⟩ := P.geodesic_family_upper_continuous (a, b) W openW
    (fun g geodesic ends => unique ⟨geodesic, ends⟩ hf ▸ fW)
  let V : Set (frontier P.body) := (fun c => (a, c)) ⁻¹' N
  have openV : IsOpen V := openN.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨U, openU, sameU⟩ := isOpen_induced_iff.mp openV
  refine ⟨source, by simpa only [first] using member, U, openU, ?_, ?_⟩
  · have bV : b ∈ V := abN
    rw [← sameU] at bV
    exact bV
  · intro x hx
    let c : frontier P.body := ⟨x, hx.2⟩
    have cV : c ∈ V := sameU ▸ hx.1
    obtain ⟨g, hg⟩ := P.geodesicFiber_nonempty a c
    have result := (formula g (contains g hg.1 (hg.2 ▸ cV)) hg.1
      ((congrArg Prod.fst hg.2).trans first.symm)).2
    have g0 : g 0 = a := congrArg Prod.fst hg.2
    have g1 : g 1 = c := congrArg Prod.snd hg.2
    simpa only [g0, g1] using result

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch
