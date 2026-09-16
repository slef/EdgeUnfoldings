import SixVertexUnfolding.Geometry.EdgeActiveSources
import SixVertexUnfolding.Geometry.EdgeTerminalCompetitors

/-! All old active sources give nearby competitors, and every new shortest
route uses one of their formulas, throughout both incident faces. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch

open Set

variable {P : ConvexPolyhedron} {center z : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} {chart : EdgeFolding facets F G} (patch : chart.MetricPatch z)
  (graph : P.SixVertexGraph)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem active_source_competitors (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ ∀ x ∈ V ∩ frontier P.body,
      ∀ source ∈ chart.activeSources a b, ∃ path : P.SurfacePath a x,
        path.length ≠ ⊤ ∧ path.length.toReal = dist source (chart.unfold x) := by
  classical
  let S := chart.activeSources a b
  letI : Fintype S := (patch.activeSources_finite graph small_faces a b different target).fintype
  have neighborhoods (source : S) : ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧
      ∀ x ∈ V ∩ frontier P.body, ∃ path : P.SurfacePath a x,
        path.length ≠ ⊤ ∧ path.length.toReal = dist source.val (chart.unfold x) := by
    obtain ⟨f, hf, terminal⟩ := source.property
    have first : f 0 = a := congrArg Prod.fst hf.2
    have last : f 1 = b := congrArg Prod.snd hf.2
    obtain ⟨V, openV, bV, competitors⟩ := patch.terminal_source_competitors graph small_faces f hf.1
      (by simpa only [first, last] using different) (by simpa only [last] using target) source terminal
    refine ⟨V, openV, by simpa only [last] using bV, ?_⟩
    intro x hx
    obtain ⟨path, finite, length⟩ := competitors x hx
    exact ⟨path.cast (congrArg Subtype.val first).symm rfl, finite, length⟩
  choose V openV bV competitors using neighborhoods
  refine ⟨⋂ source : S, V source, isOpen_iInter_of_finite openV, mem_iInter.mpr bV, ?_⟩
  intro x hx source active
  exact competitors ⟨source, active⟩ x ⟨mem_iInter.mp hx.1 ⟨source, active⟩, hx.2⟩

include graph small_faces in
theorem active_source_distance_nearby (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ ∀ x ∈ V ∩ frontier P.body,
      ∃ source ∈ chart.activeSources a b, P.surfaceDist a x = dist source (chart.unfold x) := by
  classical
  let J := P.geodesicFiber a b
  have neighborhoods (f : J) : ∃ source : Plane, chart.HasTerminalSource f.val source ∧
      ∃ W : Set P.BoundaryCurve, IsOpen W ∧ f.val ∈ W ∧
      ∀ g ∈ W, g ∈ P.geodesicCurves → g 0 = a →
        P.surfaceDist (g 0) (g 1) = dist source (chart.unfold (g 1)) := by
    have first : f.val 0 = a := congrArg Prod.fst f.property.2
    have last : f.val 1 = b := congrArg Prod.snd f.property.2
    obtain ⟨source, _, terminal, W, openW, fW, formula⟩ := patch.geodesic_branch_source graph small_faces f.val f.property.1
      (by simpa only [first, last] using different) (by simpa only [last] using target)
    exact ⟨source, terminal, W, openW, fW, fun g hg geo first_g => (formula g hg geo (first_g.trans first.symm)).2⟩
  choose source terminal W openW memberW formula using neighborhoods
  obtain ⟨N, openN, abN, near⟩ := P.geodesic_family_upper_continuous (a, b) (⋃ i : J, W i)
    (isOpen_iUnion openW) (fun f hf ends => mem_iUnion.mpr ⟨⟨f, hf, ends⟩, memberW ⟨f, hf, ends⟩⟩)
  let V : Set (frontier P.body) := (fun c => (a, c)) ⁻¹' N
  have openV : IsOpen V := openN.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨U, openU, sameU⟩ := isOpen_induced_iff.mp openV
  refine ⟨U, openU, ?_, ?_⟩
  · have bV : b ∈ V := abN
    rw [← sameU] at bV
    exact bV
  · intro x hx
    let c : frontier P.body := ⟨x, hx.2⟩
    have cV : c ∈ V := sameU ▸ hx.1
    obtain ⟨g, hg⟩ := P.geodesicFiber_nonempty a c
    obtain ⟨i, gi⟩ := mem_iUnion.mp (near g hg.1 (hg.2 ▸ cV))
    have first : g 0 = a := congrArg Prod.fst hg.2
    have last : g 1 = c := congrArg Prod.snd hg.2
    refine ⟨source i, ⟨i.val, i.property, terminal i⟩, ?_⟩
    simpa only [first, last] using formula i g gi hg.1 first

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch
