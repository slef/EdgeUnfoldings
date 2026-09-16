import SixVertexUnfolding.Geometry.EdgeRouteSourceNeighborhoods

/-! Only terminal sources of actual shortest routes are active. This set
uses the joined edge coordinates and includes targets on the crease. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G)

/-- Actual shortest-route sources at the given target, in joined coordinates. -/
def activeSources (a b : frontier P.body) : Set Plane :=
  {source | ∃ f ∈ P.geodesicFiber a b, chart.HasTerminalSource f source}

theorem activeSource_distance {z : Space} (patch : chart.MetricPatch z)
    (a b : frontier P.body) (target : (b : Space) ∈ patch.domain)
    (source : Plane) (active : source ∈ chart.activeSources a b) :
    P.surfaceDist a b = dist source (chart.unfold b) := by
  obtain ⟨f, hf, terminal⟩ := active
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  simpa only [first, last] using chart.terminal_source_distance patch f hf.1 source terminal (by simpa only [last] using target)

namespace MetricPatch

variable {chart} {z : Space} (patch : chart.MetricPatch z) (graph : P.SixVertexGraph)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem activeSources_subset (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    chart.activeSources a b ⊆ chart.sourceImages a := by
  rintro source ⟨f, hf, terminal⟩
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  obtain ⟨other, member, actual⟩ := chart.exists_terminal_source graph small_faces f hf.1
    (by simpa only [first, last] using different) (by simpa only [last] using patch.only_two _ target)
  rw [chart.terminal_source_unique f source other terminal actual]
  simpa only [first] using member

include graph small_faces in
theorem activeSources_finite (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    (chart.activeSources a b).Finite :=
  (chart.sourceImages_finite a).subset (patch.activeSources_subset graph small_faces a b different target)

include graph small_faces in
theorem activeSources_nonempty (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    (chart.activeSources a b).Nonempty := by
  obtain ⟨f, hf⟩ := P.geodesicFiber_nonempty a b
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  obtain ⟨source, _, terminal⟩ := chart.exists_terminal_source graph small_faces f hf.1
    (by simpa only [first, last] using different) (by simpa only [last] using patch.only_two _ target)
  exact ⟨source, f, hf, terminal⟩

end MetricPatch
end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
