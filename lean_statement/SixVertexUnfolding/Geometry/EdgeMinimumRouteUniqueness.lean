import SixVertexUnfolding.Geometry.EdgeLocalSourceComparison
import SixVertexUnfolding.Geometry.EdgeSingleSourceUniqueness
import SixVertexUnfolding.Geometry.ContinuousFiniteChoice

/-! An exact finite minimum in joined edge coordinates detects route
uniqueness precisely by uniqueness of its minimizing source. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch

open Set

variable {P : ConvexPolyhedron} {center z : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} {chart : EdgeFolding facets F G} (patch : chart.MetricPatch z)
  (graph : P.SixVertexGraph)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem unique_route_iff_unique_minimum (a b : frontier P.body) (different : a ≠ b)
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
    obtain ⟨actual, _, U, openU, bU, formula⟩ := patch.unique_route_source_distance graph small_faces a b different target unique
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
    apply patch.unique_route_of_local_source_formula graph small_faces a b different target p (W ∩ V) (openW.inter openV) ⟨bW, bV⟩
    intro x hx
    exact formula x ⟨hx.1.1, hx.1.2, hx.2⟩

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch
