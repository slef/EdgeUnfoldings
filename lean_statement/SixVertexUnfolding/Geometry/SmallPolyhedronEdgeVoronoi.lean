import SixVertexUnfolding.Geometry.SmallPolyhedronEdgeCompetitors
import SixVertexUnfolding.Geometry.EdgeLineCutPersistence

/-! The actual cut locus is a finite Voronoi boundary also across original
edges. The same straight-line persistence criterion therefore applies. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter BoundedContinuousFunction
open scoped Topology ENNReal

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

namespace EdgeFolding.MetricPatch

variable {center z : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} {chart : EdgeFolding facets F G} (patch : chart.MetricPatch z)

include size small_faces in
/-- The exact local minimum over old actual sources remains valid across the original edge. -/
theorem small_local_minimum_distance (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ V ⊆ patch.domain ∧ ∀ x ∈ V ∩ frontier P.body,
      (∀ source ∈ chart.activeSources a b, P.surfaceDist a x ≤ dist source (chart.unfold x)) ∧
      ∃ source ∈ chart.activeSources a b, P.surfaceDist a x = dist source (chart.unfold x) := by
  obtain ⟨U, openU, bU, competitors⟩ := patch.small_active_source_competitors size small_faces a b different target
  obtain ⟨W, openW, bW, selection⟩ := patch.small_active_source_distance_nearby size small_faces a b different target
  refine ⟨(U ∩ W) ∩ patch.domain, (openU.inter openW).inter patch.open_domain, ⟨⟨bU, bW⟩, target⟩,
    inter_subset_right, ?_⟩
  intro x hx
  refine ⟨?_, selection x ⟨hx.1.1.2, hx.2⟩⟩
  intro source active
  obtain ⟨path, finite, length⟩ := competitors x ⟨hx.1.1.1, hx.2⟩ source active
  calc
    P.surfaceDist a x ≤ path.length.toReal := ENNReal.toReal_mono finite path.surfaceEDist_le_length
    _ = dist source (chart.unfold x) := length

include size small_faces in
/-- A local source formula identifies the terminal source of every actual route ending there. -/
theorem small_terminal_source_of_local_formula (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (target : (f 1 : Space) ∈ patch.domain)
    (source : Plane) (U : Set Space) (openU : IsOpen U) (targetU : (f 1 : Space) ∈ U)
    (formula : ∀ x ∈ U ∩ frontier P.body, P.surfaceDist (f 0) x = dist source (chart.unfold x)) :
    chart.HasTerminalSource f source := by
  obtain ⟨actual, _, terminal⟩ := chart.small_exists_terminal_source size small_faces f geodesic different (patch.only_two _ target)
  let path := P.surfacePathOfCurve f
  obtain ⟨m, positive, before, inside, _⟩ := path.common_time_near_target path (U ∩ patch.domain)
    (openU.inter patch.open_domain) ⟨targetU, target⟩
  have same := patch.local_formula_identifies_source f geodesic actual source terminal target
    m positive before inside.2 U openU inside.1 formula
  rw [same]
  exact terminal

include size small_faces in
/-- A local planar source-distance formula forces uniqueness of the actual route. -/
theorem small_unique_route_of_local_source_formula (a b : frontier P.body) (different : a ≠ b)
    (target : (b : Space) ∈ patch.domain) (source : Plane) (U : Set Space) (openU : IsOpen U) (bU : (b : Space) ∈ U)
    (formula : ∀ x ∈ U ∩ frontier P.body, P.surfaceDist a x = dist source (chart.unfold x)) :
    (P.geodesicFiber a b).Subsingleton := by
  have terminal (f : P.BoundaryCurve) (hf : f ∈ P.geodesicFiber a b) : chart.HasTerminalSource f source := by
    have first : f 0 = a := congrArg Prod.fst hf.2
    have last : f 1 = b := congrArg Prod.snd hf.2
    exact patch.small_terminal_source_of_local_formula size small_faces f hf.1
      (by simpa only [first, last] using different) (by simpa only [last] using target) source U openU
      (by simpa only [last] using bU) (by simpa only [first] using formula)
  intro f hf g hg
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  exact chart.small_routes_agree_of_terminal_source size small_faces f g hf.1 hg.1
    (by simpa only [first, last] using different)
    ((congrArg Prod.fst hf.2).trans (congrArg Prod.fst hg.2).symm)
    ((congrArg Prod.snd hf.2).trans (congrArg Prod.snd hg.2).symm) source (terminal f hf) (terminal g hg)

include size small_faces in
theorem small_unique_route_iff_unique_minimum (a b : frontier P.body) (different : a ≠ b)
    (target : (b : Space) ∈ patch.domain) (sources : Set Plane) (finite : sources.Finite)
    (V : Set Space) (openV : IsOpen V) (bV : (b : Space) ∈ V) (contained : V ⊆ patch.domain)
    (minimum : ∀ x ∈ V ∩ frontier P.body,
      (∀ source ∈ sources, P.surfaceDist a x ≤ dist source (chart.unfold x)) ∧
      ∃ source ∈ sources, P.surfaceDist a x = dist source (chart.unfold x)) :
    (P.geodesicFiber a b).Subsingleton ↔
      {source ∈ sources | dist source (chart.unfold b) = P.surfaceDist a b}.Subsingleton := by
  classical
  constructor
  · intro unique
    obtain ⟨actual, _, U, openU, bU, formula⟩ := patch.small_unique_route_source_distance size small_faces a b different target unique
    have identifies (source : Plane) (member : source ∈ sources)
        (attains : dist source (chart.unfold b) = P.surfaceDist a b) : actual = source := by
      apply patch.local_source_comparison_eq b target actual source (U ∩ V) (openU.inter openV) ⟨bU, bV⟩
      · intro x hx
        rw [← formula x ⟨hx.1.1, hx.2⟩]
        exact (minimum x ⟨hx.1.2, hx.2⟩).1 source member
      · rw [← formula b ⟨bU, b.property⟩, attains]
    intro p hp q hq
    exact (identifies p hp.1 hp.2).symm.trans (identifies q hq.1 hq.2)
  · intro unique
    letI : Fintype sources := finite.fintype
    obtain ⟨p, member, at_b⟩ := (minimum b ⟨bV, b.property⟩).2
    let S := V ∩ frontier P.body
    let formulas (q : sources) (x : Space) := dist q.val (chart.unfold x)
    have selected (x : Space) (hx : x ∈ S) : ∃ q : sources, P.surfaceDist a x = formulas q x := by
      obtain ⟨q, hq, equal⟩ := (minimum x hx).2
      exact ⟨⟨q, hq⟩, equal⟩
    have separated (q : sources) (distinct : q ≠ ⟨p, member⟩) : formulas ⟨p, member⟩ b ≠ formulas q b := by
      intro equal
      apply distinct
      apply Subtype.ext
      exact unique ⟨q.property, equal.symm.trans at_b.symm⟩ ⟨member, at_b.symm⟩
    have coordinates : ContinuousOn chart.unfold S := patch.unfold_continuousOn.mono (fun _ hx => ⟨contained hx.1, hx.2⟩)
    obtain ⟨W, openW, bW, formula⟩ := continuous_finite_choice_local S (P.surfaceDist a) formulas
      ((P.surfaceDist_continuousOn a.property).mono (fun _ hx => hx.2))
      (fun _ => (continuous_const.dist continuous_id).comp_continuousOn coordinates)
      selected b ⟨bV, b.property⟩ ⟨p, member⟩ at_b separated
    apply patch.small_unique_route_of_local_source_formula size small_faces a b different target p (W ∩ V) (openW.inter openV) ⟨bW, bV⟩
    intro x hx
    exact formula x ⟨hx.1.1, hx.1.2, hx.2⟩

include size small_faces in
/-- Nearby multiple-route points are exactly ties between nearest old active sources on both sides of the crease. -/
theorem small_local_voronoi_cut_locus (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ V ⊆ patch.domain ∧ ∀ x ∈ V ∩ frontier P.body,
      (x ∈ P.multipleRouteLocus a ↔ chart.unfold x ∈ voronoiBoundary (chart.activeSources a b)) := by
  obtain ⟨U, openU, bU, contained, minimum⟩ := patch.small_local_minimum_distance size small_faces a b different target
  refine ⟨U ∩ ({(a : Space)}ᶜ : Set Space), openU.inter isClosed_singleton.isOpen_compl,
    ⟨bU, fun same => different (Subtype.ext same.symm)⟩, inter_subset_left.trans contained, ?_⟩
  intro x hx
  let c : frontier P.body := ⟨x, hx.2⟩
  have distinct_c : a ≠ c := fun same => hx.1.2 (congrArg Subtype.val same.symm)
  have criterion := patch.small_unique_route_iff_unique_minimum size small_faces a c distinct_c (contained hx.1.1)
    (chart.activeSources a b) (patch.small_activeSources_finite size small_faces a b different target)
    U openU hx.1.1 contained minimum
  have value := minimum x ⟨hx.1.1, hx.2⟩
  have ties := mem_voronoiBoundary_iff_multiple_minima (chart.activeSources a b) (chart.unfold x)
    (P.surfaceDist a x) value.1 value.2
  change (c : Space) ∈ P.multipleRouteLocus a ↔ _
  rw [P.multiple_routes_iff_fiber a c, and_iff_right distinct_c]
  exact criterion.not.trans ties.symm

end EdgeFolding.MetricPatch

namespace EdgeFolding

variable {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G)

include size small_faces in
theorem small_cut_persists_along_line (a : frontier P.body) (shared : P.ShareEdge F G)
    (curve : ℝ →ᵃ[ℝ] Space) {t : ℝ} (target : curve t ∈ F.val ∩ G.val)
    (not_vertex : curve t ∉ P.vertices) (cut : curve t ∈ P.multipleRouteLocus a)
    (regular : t ∉ lineSourceCrossings (chart.sourceImages a) (chart.left.comp curve)) :
    ∃ J : Set ℝ, IsOpen J ∧ t ∈ J ∧ ∀ s ∈ J, curve s ∈ F.val → curve s ∈ P.multipleRouteLocus a := by
  let b : frontier P.body := ⟨curve t, F.subset_frontier target.1⟩
  have different : a ≠ b := ((P.multiple_routes_iff_fiber a b).mp cut).1
  obtain ⟨patch⟩ := chart.exists_metric_patch shared target not_vertex
  obtain ⟨V, openV, bV, _, diagram⟩ := patch.small_local_voronoi_cut_locus size small_faces a b different patch.center_mem
  have coordinate : chart.unfold b = (chart.left.comp curve) t := chart.unfold_of_first target.1
  have contained := patch.small_activeSources_subset size small_faces a b different patch.center_mem
  have common (p : Plane) (hp : p ∈ chart.activeSources a b) (q : Plane) (hq : q ∈ chart.activeSources a b) :
      dist p ((chart.left.comp curve) t) = dist q ((chart.left.comp curve) t) := by
    rw [← coordinate]
    exact (chart.activeSource_distance patch a b patch.center_mem p hp).symm.trans
      (chart.activeSource_distance patch a b patch.center_mem q hq)
  have boundary : (chart.left.comp curve) t ∈ voronoiBoundary (chart.activeSources a b) := by
    rw [← coordinate]
    exact (diagram _ ⟨bV, b.property⟩).mp cut
  have all_tied := voronoi_ties_persist_on_line (chart.sourceImages a) (chart.activeSources a b)
    contained (chart.left.comp curve) regular common boundary
  refine ⟨curve ⁻¹' V, openV.preimage curve.continuous_of_finiteDimensional, bV, ?_⟩
  intro s hs in_face
  apply (diagram _ ⟨hs, F.subset_frontier in_face⟩).mpr
  rw [chart.unfold_of_first in_face]
  exact all_tied s

end EdgeFolding

end SixVertexUnfolding.ConvexPolyhedron
