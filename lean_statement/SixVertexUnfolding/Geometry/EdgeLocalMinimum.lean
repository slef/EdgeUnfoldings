import SixVertexUnfolding.Geometry.EdgeActiveSourceNeighborhoods

/-! Intrinsic distance is locally a finite minimum in the joined edge
development, with genuine competitors for every active source. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch

open Set

variable {P : ConvexPolyhedron} {center z : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} {chart : EdgeFolding facets F G} (patch : chart.MetricPatch z)
  (graph : P.SixVertexGraph)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The exact local minimum over old actual sources remains valid across the original edge. -/
theorem local_minimum_distance (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ V ⊆ patch.domain ∧ ∀ x ∈ V ∩ frontier P.body,
      (∀ source ∈ chart.activeSources a b, P.surfaceDist a x ≤ dist source (chart.unfold x)) ∧
      ∃ source ∈ chart.activeSources a b, P.surfaceDist a x = dist source (chart.unfold x) := by
  obtain ⟨U, openU, bU, competitors⟩ := patch.active_source_competitors graph small_faces a b different target
  obtain ⟨W, openW, bW, selection⟩ := patch.active_source_distance_nearby graph small_faces a b different target
  refine ⟨(U ∩ W) ∩ patch.domain, (openU.inter openW).inter patch.open_domain, ⟨⟨bU, bW⟩, target⟩,
    inter_subset_right, ?_⟩
  intro x hx
  refine ⟨?_, selection x ⟨hx.1.1.2, hx.2⟩⟩
  intro source active
  obtain ⟨path, finite, length⟩ := competitors x ⟨hx.1.1.1, hx.2⟩ source active
  calc
    P.surfaceDist a x ≤ path.length.toReal := ENNReal.toReal_mono finite path.surfaceEDist_le_length
    _ = dist source (chart.unfold x) := length

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch
