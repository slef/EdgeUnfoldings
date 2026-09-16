import SixVertexUnfolding.Geometry.JunctionIncidence
import SixVertexUnfolding.Geometry.CircularGapData
import SixVertexUnfolding.Geometry.CutTreeTargets

/-! One constructed order for all incident edges at an actual nonvertex
cut-tree vertex. All source labels and ray positions use a common chart.
-/

namespace SixVertexUnfolding.ConvexPolyhedron

open Real Set

/-- The finite circular order and its geometric correspondence with the tree. -/
structure JunctionOrder {P : ConvexPolyhedron} {a : frontier P.body}
    (T : P.CutLocusTree a) (u : T.vertices) where
  chart : P.CutVoronoiChart a (T.vertexTarget u)
  sites : Fin chart.sources.ncard ≃ chart.sources
  angles : Fin chart.sources.ncard → ℝ
  increasing : StrictMono angles
  bounds : ∀ i, 0 ≤ angles i ∧ angles i < 2 * π
  position : ∀ i, (sites i : Plane) =
    chart.origin + P.surfaceDist a (T.vertexTarget u) • direction (angles i)
  first : Fin chart.sources.ncard
  last : Fin chart.sources.ncard
  at_first : first.val = 0
  at_last : last.val + 1 = chart.sources.ncard
  two : first < last
  neighbors : circularGapMidpoints angles first last ≃ {v : T.vertices // T.graph.Adj u v}
  radius : ℝ
  radius_positive : 0 < radius
  rays : ∀ m, ∀ ρ ∈ Ioo (0 : ℝ) radius,
    chart.map (chart.origin + ρ • direction m) ∈
      openSegment ℝ (u : Space) ((neighbors m).val : Space)

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Every nonvertex tree vertex has one actual circular order of all its
incident edges, together with their complete local ray correspondence. -/
theorem exists_junction_order (a : frontier P.body) (T : P.CutLocusTree a)
    (u : T.vertices) (not_vertex : (u : Space) ∉ P.vertices) : Nonempty (JunctionOrder T u) := by
  let b := T.vertexTarget u
  have different : a ≠ b := T.vertexTarget_different u
  obtain ⟨chart⟩ := graph.cut_voronoi_chart small_faces a b different not_vertex
  have multiple : (b : Space) ∈ P.multipleRouteLocus a := by
    rcases T.vertexTarget_cut u with multiple | original
    · exact multiple
    · exact (not_vertex original.1).elim
  have center : chart.origin ∈ voronoiBoundary chart.sources :=
    (chart.cut_diagram chart.origin chart.origin_mem).mp (chart.at_origin.symm ▸ multiple)
  obtain ⟨p, hp, q, hq, distinct, _⟩ := center
  have count : 1 < chart.sources.ncard := (one_lt_ncard chart.finite_sources).mpr
    ⟨p, hp, q, hq, distinct⟩
  have radius_positive : 0 < P.surfaceDist a b := by
    simpa using CutVoronoiChart.tail_radius_pos different (0 : unitInterval)
      (by change (0 : ℝ) < 1; norm_num)
  obtain ⟨sites, θ, increasing, bounds, position⟩ := exists_circular_source_order chart.sources
    chart.finite_sources chart.origin (P.surfaceDist a b) radius_positive chart.source_distance
  let first : Fin chart.sources.ncard := ⟨0, by omega⟩
  let last : Fin chart.sources.ncard := ⟨chart.sources.ncard - 1, by omega⟩
  have at_last : last.val + 1 = chart.sources.ncard := by dsimp [last]; omega
  have two : first < last := by change 0 < chart.sources.ncard - 1; omega
  obtain ⟨ε, positive, neighbors, rays⟩ := chart.gap_rays_equiv_neighbors T.toEmbeddedCutGraph
    u.property different not_vertex sites θ increasing bounds position first last rfl at_last two
  exact ⟨⟨chart, sites, θ, increasing, bounds, position, first, last, rfl, at_last, two,
    neighbors, ε, positive, rays⟩⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
