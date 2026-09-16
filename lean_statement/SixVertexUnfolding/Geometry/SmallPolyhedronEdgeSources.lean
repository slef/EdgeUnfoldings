import SixVertexUnfolding.Geometry.SmallPolyhedronRoutePrefixes
import SixVertexUnfolding.Geometry.EdgeActiveSourceRoutes

/-! Terminal sources in joined coordinates across an original edge. Actual
routes with the same source copy coincide, and the source is locally stable. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter BoundedContinuousFunction
open scoped Topology ENNReal

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

namespace EdgeFolding

variable {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G)

include size small_faces in
theorem small_routes_agree_of_terminal_source (f g : P.BoundaryCurve)
    (hf : f ∈ P.geodesicCurves) (hg : g ∈ P.geodesicCurves) (different : f 0 ≠ f 1)
    (first : f 0 = g 0) (last : f 1 = g 1) (source : Plane)
    (left : chart.HasTerminalSource f source) (right : chart.HasTerminalSource g source) : f = g := by
  obtain ⟨s, s_before, left⟩ := left
  obtain ⟨u, u_before, right⟩ := right
  obtain ⟨t, after, before⟩ := exists_between (max_lt s_before u_before)
  have left_t := left t ⟨(le_max_left s u).trans after.le, before.le⟩
  have right_t := right t ⟨(le_max_right s u).trans after.le, before.le⟩
  have coordinates : chart.unfold (f t) = chart.unfold (g t) := by rw [left_t.2, right_t.2, last]
  have meet : f t = g t := by
    apply Subtype.ext
    have equal := congrArg chart.fold.map coordinates
    rwa [chart.fold_unfold left_t.1, chart.fold_unfold right_t.1] at equal
  exact small_geodesic_curves_agree_of_meeting size small_faces f g hf hg different first last t
    ((unitInterval.nonneg s).trans_lt ((le_max_left s u).trans_lt after)) before meet

end EdgeFolding

namespace EdgeFolding.MetricPatch

variable {center z : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} {chart : EdgeFolding facets F G} (patch : chart.MetricPatch z)

include size small_faces in
/-- Nearby shortest routes from the same source have the same actual terminal source in the joined chart. -/
theorem small_geodesic_branch_source (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
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
  obtain ⟨source, member, terminal⟩ := chart.small_exists_terminal_source size small_faces f geodesic different (patch.only_two _ target)
  have original := chart.recoveredSource_of_terminal f geodesic source terminal
    patch.domain patch.open_domain target patch.metric t before ftU
  refine ⟨source, member, terminal, W, openW, ⟨ftU, target, different, fV⟩, ?_⟩
  intro g near shortest same_start
  obtain ⟨other, member_g, terminal_g⟩ := chart.small_exists_terminal_source size small_faces g shortest near.2.2.1
    (patch.only_two _ near.2.1)
  have recovered := chart.recoveredSource_of_terminal g shortest other terminal_g
    patch.domain patch.open_domain near.2.1 patch.metric t before near.1
  have candidate : chart.recoveredSource t g ∈ chart.sourceImages (f 0) := by
    rw [recovered, ← same_start]
    exact member_g
  have same : other = source := recovered.symm.trans ((isolated g near.2.2.2 candidate).trans original)
  rw [same] at terminal_g
  exact ⟨terminal_g, chart.terminal_source_distance patch g shortest source terminal_g near.2.1⟩

include size small_faces in
/-- A unique route to any point in this edge patch has one local distance formula in the same joined coordinates. -/
theorem small_unique_route_source_distance (a b : frontier P.body) (different : a ≠ b)
    (target : (b : Space) ∈ patch.domain) (unique : (P.geodesicFiber a b).Subsingleton) :
    ∃ source ∈ chart.sourceImages a, ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧
      ∀ x ∈ V ∩ frontier P.body, P.surfaceDist a x = dist source (chart.unfold x) := by
  obtain ⟨f, hf⟩ := P.geodesicFiber_nonempty a b
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  obtain ⟨source, member, _, W, openW, fW, formula⟩ := patch.small_geodesic_branch_source size small_faces f hf.1
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

include size small_faces in
theorem small_activeSources_subset (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    chart.activeSources a b ⊆ chart.sourceImages a := by
  rintro source ⟨f, hf, terminal⟩
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  obtain ⟨other, member, actual⟩ := chart.small_exists_terminal_source size small_faces f hf.1
    (by simpa only [first, last] using different) (by simpa only [last] using patch.only_two _ target)
  rw [chart.terminal_source_unique f source other terminal actual]
  simpa only [first] using member

include size small_faces in
theorem small_activeSources_finite (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    (chart.activeSources a b).Finite :=
  (chart.sourceImages_finite a).subset (patch.small_activeSources_subset size small_faces a b different target)

include size small_faces in
theorem small_activeSources_nonempty (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    (chart.activeSources a b).Nonempty := by
  obtain ⟨f, hf⟩ := P.geodesicFiber_nonempty a b
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  obtain ⟨source, _, terminal⟩ := chart.small_exists_terminal_source size small_faces f hf.1
    (by simpa only [first, last] using different) (by simpa only [last] using patch.only_two _ target)
  exact ⟨source, f, hf, terminal⟩

include size small_faces in
theorem small_routes_equiv_active_sources (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    Nonempty (P.geodesicFiber a b ≃ chart.activeSources a b) := by
  classical
  have sources (f : P.geodesicFiber a b) : ∃ source, chart.HasTerminalSource f.val source := by
    have first : f.val 0 = a := congrArg Prod.fst f.property.2
    have last : f.val 1 = b := congrArg Prod.snd f.property.2
    obtain ⟨source, _, terminal⟩ := chart.small_exists_terminal_source size small_faces f.val f.property.1
      (by simpa only [first, last] using different) (by simpa only [last] using patch.only_two _ target)
    exact ⟨source, terminal⟩
  choose source terminal using sources
  let code (f : P.geodesicFiber a b) : chart.activeSources a b := ⟨source f, f.val, f.property, terminal f⟩
  have injective : Function.Injective code := by
    intro f g equal
    apply Subtype.ext
    have first : f.val 0 = a := congrArg Prod.fst f.property.2
    have last : f.val 1 = b := congrArg Prod.snd f.property.2
    apply chart.small_routes_agree_of_terminal_source size small_faces f.val g.val f.property.1 g.property.1
      (by simpa only [first, last] using different)
      ((congrArg Prod.fst f.property.2).trans (congrArg Prod.fst g.property.2).symm)
      ((congrArg Prod.snd f.property.2).trans (congrArg Prod.snd g.property.2).symm) (source f) (terminal f)
    have same : source f = source g := congrArg Subtype.val equal
    rw [same]
    exact terminal g
  have surjective : Function.Surjective code := by
    intro q
    obtain ⟨f, hf, actual⟩ := q.property
    refine ⟨⟨f, hf⟩, Subtype.ext ?_⟩
    exact chart.terminal_source_unique f _ q (terminal ⟨f, hf⟩) actual
  exact ⟨Equiv.ofBijective code ⟨injective, surjective⟩⟩

include size small_faces in
theorem small_activeSources_ncard (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    (chart.activeSources a b).ncard = Nat.card (P.geodesicFiber a b) := by
  obtain ⟨equiv⟩ := patch.small_routes_equiv_active_sources size small_faces a b different target
  exact (Nat.card_congr equiv).symm

end EdgeFolding.MetricPatch

end SixVertexUnfolding.ConvexPolyhedron
