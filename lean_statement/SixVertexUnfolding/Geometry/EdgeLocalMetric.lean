import SixVertexUnfolding.Geometry.EdgeSegmentPaths
import SixVertexUnfolding.Geometry.ShortestLocalization

/-! A sufficiently small developed disk at an edge preserves the actual
intrinsic surface distance. Globally shortest competitors cannot escape this neighborhood. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.Neighborhood

open Set

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} {chart : EdgeFolding facets F G} {z : Space} (near : chart.Neighborhood z)

/-- In a small disk centered at a nonvertex edge point, planar and intrinsic distances agree. -/
theorem exists_isometric_disk (shared : P.ShareEdge F G) (hz : z ∈ F.val ∩ G.val)
    (not_vertex : z ∉ P.vertices) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (chart.left z) ε ⊆ near.domain ∧
      ∀ x ∈ Metric.ball (chart.left z) ε, ∀ y ∈ Metric.ball (chart.left z) ε,
        P.surfaceDist (chart.fold.map x) (chart.fold.map y) = dist x y := by
  obtain ⟨U, openU, zU, only_two⟩ := P.edge_neighborhood_two_facets F G shared hz not_vertex
  obtain ⟨r, r_positive, ballU⟩ := Metric.isOpen_iff.mp openU z zU
  obtain ⟨ρ, ρ_positive, ballV⟩ := Metric.isOpen_iff.mp near.open_domain (chart.left z) near.origin_mem
  let ε := min ρ (r / 4)
  have ε_positive : 0 < ε := lt_min ρ_positive (div_pos r_positive (by norm_num))
  have ε_small : ε ≤ r / 4 := min_le_right _ _
  have disk_in : Metric.ball (chart.left z) ε ⊆ near.domain := by
    intro x hx
    apply ballV
    change dist x (chart.left z) < ρ
    exact hx.trans_le (min_le_left _ _)
  refine ⟨ε, ε_positive, disk_in, ?_⟩
  intro x hx y hy
  have segment_in : segment ℝ x y ⊆ near.domain :=
    ((convex_ball (chart.left z) ε).segment_subset hx hy).trans disk_in
  let comparison := near.segmentPath x y segment_in
  have length : comparison.length = edist x y := near.segmentPath_length x y segment_in
  have comparison_finite : comparison.length ≠ ⊤ := length ▸ edist_ne_top x y
  have first_surface := near.on_surface ⟨x, disk_in hx, rfl⟩
  have second_surface := near.on_surface ⟨y, disk_in hy, rfl⟩
  obtain ⟨path, shortest, finite⟩ := P.exists_shortest_surface_path first_surface second_surface
  have folded_offset : dist (chart.fold.map x) z ≤ dist x (chart.left z) := by
    have bound := chart.fold.lipschitz.dist_le_mul x (chart.left z)
    simpa only [chart.fold_left hz.1, NNReal.coe_one, one_mul] using bound
  have budget : comparison.length.toReal + dist (chart.fold.map x) z < r := by
    rw [length, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    have across := dist_triangle x (chart.left z) y
    rw [dist_comm (chart.left z) y] at across
    change dist x (chart.left z) < ε at hx
    change dist y (chart.left z) < ε at hy
    linarith
  have contained : ∀ t, path.curve t ∈ F.val ∪ G.val := by
    intro t
    exact only_two ⟨ballU (path.shortest_range_in_ball shortest comparison comparison_finite z r budget t), path.on_surface t⟩
  have lower := chart.unfolded_chord_le_length path contained
  rw [Neighborhood.unfold_fold chart near (disk_in hx),
    Neighborhood.unfold_fold chart near (disk_in hy)] at lower
  have upper : path.length ≤ edist x y := (shortest comparison).trans_eq length
  have exact_length := le_antisymm upper lower
  rw [surfaceDist, ← path.length_eq_surfaceEDist shortest, exact_length, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.Neighborhood
