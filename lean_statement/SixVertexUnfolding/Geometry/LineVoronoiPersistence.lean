import SixVertexUnfolding.Geometry.LineSourceCrossings
import SixVertexUnfolding.Geometry.VoronoiDiagram

/-! At a nonexceptional line parameter, a tied active source family
remains tied along the entire line. -/

namespace SixVertexUnfolding

open Set

theorem voronoi_ties_persist_on_line (candidates sources : Set Plane)
    (contained : sources ⊆ candidates) (line : ℝ →ᵃ[ℝ] Plane) {t : ℝ}
    (regular : t ∉ lineSourceCrossings candidates line)
    (common : ∀ p ∈ sources, ∀ q ∈ sources, dist p (line t) = dist q (line t))
    (boundary : line t ∈ voronoiBoundary sources) :
    ∀ s, line s ∈ voronoiBoundary sources := by
  obtain ⟨p, hp, q, hq, different, _⟩ := boundary
  have tied (r : Plane) (hr : r ∈ sources) := source_tie_persists_on_line candidates line regular
    (contained hp) (contained hr) (common p hp r hr)
  intro s
  exact ⟨p, hp, q, hq, different, tied q hq s, fun r hr => (tied r hr s).le⟩

end SixVertexUnfolding
