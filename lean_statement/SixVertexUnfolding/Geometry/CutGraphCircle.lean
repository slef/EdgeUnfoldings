import SixVertexUnfolding.Geometry.EmbeddedGraphStars
import SixVertexUnfolding.Geometry.CutArcNotLeaf
import SixVertexUnfolding.Geometry.FlatChartCoordinates

/-! A small metric circle in a flat chart meets each incident cut-graph
edge exactly once. The resulting bijection retains which actual edge
contains each circle point, rather than only comparing their cardinalities.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} (K : P.EmbeddedCutGraph a)

/-- The actual cut trace on a planar circle in a flat chart. -/
def circleTrace {u : K.vertices} (chart : P.FlatChart (u : Space)) (ρ : ℝ) : Set Plane :=
  {x | x ∈ chart.domain ∧ dist x chart.origin = ρ ∧ chart.map x ∈ P.cutSetInSpace a}

private theorem segment_point_at_radius (u v : Space) {ρ : ℝ}
    (positive : 0 < ρ) (short : ρ < dist u v) :
    ∃ p ∈ openSegment ℝ u v, dist u p = ρ := by
  have length_positive : 0 < dist u v := positive.trans short
  let t := ρ / dist u v
  have between : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos positive length_positive, (div_lt_one length_positive).mpr short⟩
  refine ⟨AffineMap.lineMap u v t, lineMap_mem_openSegment ℝ u v between, ?_⟩
  rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_pos between.1]
  exact div_mul_cancel₀ ρ length_positive.ne'

/-- Every sufficiently small circle has one point on each incident edge,
and every cut point on that circle comes from one of those edges. -/
theorem neighbors_equiv_circle (u : K.vertices) (chart : P.FlatChart (u : Space)) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε,
      ∃ e : {v : K.vertices // K.graph.Adj u v} ≃ K.circleTrace chart ρ,
        ∀ v, chart.map (e v) ∈ openSegment ℝ (u : Space) (v.val : Space) := by
  classical
  obtain ⟨cover, open_cover, center_cover, covers⟩ := chart.covers
  obtain ⟨star, open_star, center_star, local_star⟩ := K.vertex_star_neighborhood u
  let avoid := (K.vertices \ {(u : Space)})ᶜ
  have open_avoid : IsOpen avoid := (K.finite_vertices.subset diff_subset).isClosed.isOpen_compl
  have center_avoid : (u : Space) ∈ avoid := fun h => h.2 rfl
  obtain ⟨δ, delta_positive, ambient_disk⟩ := Metric.isOpen_iff.mp
    (open_cover.inter open_avoid) u ⟨center_cover, center_avoid⟩
  have edges_long (v : {v : K.vertices // K.graph.Adj u v}) : δ ≤ dist (u : Space) (v.val : Space) := by
    by_contra short
    have inside := ambient_disk (show (v.val : Space) ∈ Metric.ball (u : Space) δ by
      change dist (v.val : Space) (u : Space) < δ
      rw [dist_comm]
      exact lt_of_not_ge short)
    exact inside.2 ⟨v.val.property, fun same => v.property.ne (Subtype.ext same.symm)⟩
  obtain ⟨η, eta_positive, chart_disk⟩ := Metric.isOpen_iff.mp
    (chart.open_domain.inter (open_star.preimage chart.continuous)) chart.origin
    ⟨chart.origin_mem, by change chart.map chart.origin ∈ star; rwa [chart.at_origin]⟩
  refine ⟨min δ η, lt_min delta_positive eta_positive, ?_⟩
  intro ρ hr
  have small_ambient : ρ < δ := hr.2.trans_le (min_le_left _ _)
  have small_chart : ρ < η := hr.2.trans_le (min_le_right _ _)
  have sample (v : {v : K.vertices // K.graph.Adj u v}) :
      ∃ x : K.circleTrace chart ρ,
        chart.map x ∈ openSegment ℝ (u : Space) (v.val : Space) := by
    obtain ⟨p, on_edge, radius⟩ := segment_point_at_radius (u : Space) (v.val : Space)
      hr.1 (small_ambient.trans_le (edges_long v))
    have closed_edge := openSegment_subset_segment ℝ _ _ on_edge
    have cut := K.closed_edge_in_trace v.property closed_edge
    have surface := P.cutSetInSpace_subset_boundary a cut
    have in_cover := (ambient_disk (show p ∈ Metric.ball (u : Space) δ by
      change dist p (u : Space) < δ
      rw [dist_comm, radius]
      exact small_ambient)).1
    obtain ⟨x, inside, mapped⟩ := covers ⟨in_cover, surface⟩
    obtain ⟨F, cofacial⟩ := K.cofacial_edges u v.val v.property
    have distance := chart.distance chart.origin chart.origin_mem x inside
    rw [chart.at_origin, mapped, P.surfaceDist_eq_dist_in_face F
      (cofacial (left_mem_segment ℝ _ _)) (cofacial closed_edge)] at distance
    have circle : dist x chart.origin = ρ := (dist_comm _ _).trans (distance.symm.trans radius)
    exact ⟨⟨x, inside, circle, by rwa [mapped]⟩, by rwa [mapped]⟩
  choose point on_edge using sample
  have intrinsic_radius (x : K.circleTrace chart ρ) : P.surfaceDist u (chart.map x) = ρ := by
    have distance := chart.distance chart.origin chart.origin_mem x x.property.1
    rw [chart.at_origin, dist_comm chart.origin x, x.property.2.1] at distance
    exact distance
  have injective : Function.Injective point := by
    intro v w same
    have same_map := congrArg (fun x : K.circleTrace chart ρ => chart.map x) same
    dsimp only at same_map
    have on_other : chart.map (point v) ∈ openSegment ℝ (u : Space) (w.val : Space) := by
      rw [same_map]
      exact on_edge w
    rcases K.open_edges_meet u v.val u w.val v.property w.property (chart.map (point v))
      (on_edge v) on_other with ⟨_, equal⟩ | ⟨_, reversed⟩
    · exact Subtype.ext equal
    · exact (v.property.ne reversed.symm).elim
  have surjective : Function.Surjective point := by
    intro x
    have near := chart_disk (show (x : Plane) ∈ Metric.ball chart.origin η by
      change dist (x : Plane) chart.origin < η
      rw [x.property.2.1]
      exact small_chart)
    rcases local_star (chart.map x) near.2 x.property.2.2 with at_center | ⟨v, edge, member⟩
    · have radius := intrinsic_radius x
      rw [at_center, P.surfaceDist_self (P.cutSetInSpace_subset_boundary a (K.vertex_in_trace u))] at radius
      linarith [hr.1]
    · let neighbor : {v : K.vertices // K.graph.Adj u v} := ⟨v, edge⟩
      have point_on_edge := openSegment_subset_segment ℝ _ _ (on_edge neighbor)
      obtain ⟨F, cofacial⟩ := K.cofacial_edges u v edge
      have from_center (y : K.circleTrace chart ρ)
          (on_segment : chart.map y ∈ segment ℝ (u : Space) (v : Space)) :
          dist (u : Space) (chart.map y) = ρ := by
        rw [← P.surfaceDist_eq_dist_in_face F (cofacial (left_mem_segment ℝ _ _)) (cofacial on_segment)]
        exact intrinsic_radius y
      have same_map := space_segment_point_unique (u : Space) (v : Space)
        (chart.map (point neighbor)) (chart.map x) point_on_edge member
        ((from_center (point neighbor) point_on_edge).trans (from_center x member).symm)
      exact ⟨neighbor, Subtype.ext (chart.injective (point neighbor).property.1 x.property.1 same_map)⟩
  exact ⟨Equiv.ofBijective point ⟨injective, surjective⟩, on_edge⟩

end SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph
