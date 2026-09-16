import SixVertexUnfolding.Geometry.EdgeActiveSources
import SixVertexUnfolding.Geometry.GeodesicCurveNonbranching

/-! Actual terminal sources count shortest routes exactly in a joined edge
development. Agreement on the crease creates no duplicate source codes. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G) (graph : P.SixVertexGraph)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem routes_agree_of_terminal_source (f g : P.BoundaryCurve)
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
  exact graph.geodesic_curves_agree_of_meeting small_faces f g hf hg different first last t
    ((unitInterval.nonneg s).trans_lt ((le_max_left s u).trans_lt after)) before meet

namespace MetricPatch

variable {chart} {z : Space} (patch : chart.MetricPatch z)

include graph small_faces in
theorem routes_equiv_active_sources (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    Nonempty (P.geodesicFiber a b ≃ chart.activeSources a b) := by
  classical
  have sources (f : P.geodesicFiber a b) : ∃ source, chart.HasTerminalSource f.val source := by
    have first : f.val 0 = a := congrArg Prod.fst f.property.2
    have last : f.val 1 = b := congrArg Prod.snd f.property.2
    obtain ⟨source, _, terminal⟩ := chart.exists_terminal_source graph small_faces f.val f.property.1
      (by simpa only [first, last] using different) (by simpa only [last] using patch.only_two _ target)
    exact ⟨source, terminal⟩
  choose source terminal using sources
  let code (f : P.geodesicFiber a b) : chart.activeSources a b := ⟨source f, f.val, f.property, terminal f⟩
  have injective : Function.Injective code := by
    intro f g equal
    apply Subtype.ext
    have first : f.val 0 = a := congrArg Prod.fst f.property.2
    have last : f.val 1 = b := congrArg Prod.snd f.property.2
    apply chart.routes_agree_of_terminal_source graph small_faces f.val g.val f.property.1 g.property.1
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

include graph small_faces in
theorem activeSources_ncard (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    (chart.activeSources a b).ncard = Nat.card (P.geodesicFiber a b) := by
  obtain ⟨equiv⟩ := patch.routes_equiv_active_sources graph small_faces a b different target
  exact (Nat.card_congr equiv).symm

end MetricPatch
end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
