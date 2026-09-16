import SixVertexUnfolding.Geometry.JunctionOrder
import SixVertexUnfolding.Geometry.SmallPolyhedronCutVoronoiCharts

/-! One constructed order for all incident edges at an actual nonvertex
cut-tree vertex. All source labels and ray positions use a common chart.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Real Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Every nonvertex tree vertex has one actual circular order of all its
incident edges, together with their complete local ray correspondence. -/
theorem small_exists_junction_order (a : frontier P.body) (T : P.CutLocusTree a)
    (u : T.vertices) (not_vertex : (u : Space) ∉ P.vertices) : Nonempty (JunctionOrder T u) := by
  let b := T.vertexTarget u
  have different : a ≠ b := T.vertexTarget_different u
  obtain ⟨chart⟩ := small_cut_voronoi_chart size small_faces a b different not_vertex
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

end SixVertexUnfolding.ConvexPolyhedron
