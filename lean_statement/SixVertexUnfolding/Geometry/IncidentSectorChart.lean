import SixVertexUnfolding.Geometry.IncidentCornerChart
import SixVertexUnfolding.Geometry.SmallRadialSectors

/-! Each labelled triangle fills a uniform small angular sector of
the actual junction chart, with its complete surface placement preserved. -/

namespace SixVertexUnfolding.ConvexPolyhedron.IncidentTriangles

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v}
    {chart : P.CutVoronoiChart a (T.vertexTarget u)} {angle : ℝ}
    (D : IncidentTriangles T edge chart angle)

theorem exists_chart_sector (side : Bool) {radius R θ : ℝ} (positive : 0 < radius)
    (ray : ∀ ρ ∈ Ioo (0 : ℝ) radius,
      chart.map (chart.origin + ρ • direction angle) ∈ openSegment ℝ (u : Space) (v : Space))
    (R_positive : 0 < R)
    (source_position : D.motion (D.apex side) = chart.origin + R • direction θ)
    (different : θ ≠ angle) (width : |angle - θ| < Real.pi) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε, ∀ φ ∈ Icc (min θ angle) (max θ angle),
      let x := chart.origin + ρ • direction φ
      ∃ inside : x ∈ chart.domain, D.placed.Places ⟨chart.map x, chart.on_surface inside⟩ x := by
  obtain ⟨s, t, sp, _, tp, _, contained, in_domain, agrees⟩ := D.exists_chart_corner side positive ray
  have length_positive : 0 < dist (u : Space) (v : Space) := by
    apply dist_pos.mpr
    intro same
    exact edge.ne (Subtype.ext same)
  have q_formula : AffineMap.lineMap chart.origin (D.motion (D.apex side)) (s : ℝ) =
      chart.origin + ((s : ℝ) * R) • direction θ := by
    rw [source_position, AffineMap.lineMap_apply_module]
    module
  have r_formula : AffineMap.lineMap chart.origin (D.motion D.model.right) (t : ℝ) =
      chart.origin + ((t : ℝ) * dist (u : Space) (v : Space)) • direction angle := by
    rw [D.at_neighbor, AffineMap.lineMap_apply_module]
    module
  obtain ⟨ε, ep, sector⟩ := triangle_small_sector_unordered chart.origin
    ((s : ℝ) * R) ((t : ℝ) * dist (u : Space) (v : Space)) θ angle
    (mul_pos sp R_positive) (mul_pos tp length_positive) different width
  refine ⟨ε, ep, ?_⟩
  intro ρ hr φ hφ
  let x := chart.origin + ρ • direction φ
  have member : x ∈ convexHull ℝ
      ({AffineMap.lineMap chart.origin (D.motion (D.apex side)) (s : ℝ), chart.origin,
        AffineMap.lineMap chart.origin (D.motion D.model.right) (t : ℝ)} : Set Plane) := by
    rw [q_formula, r_formula]
    exact sector ρ hr φ hφ
  have inside := in_domain member
  refine ⟨inside, ?_⟩
  let H := D.placed.sideTriangle side
  have folded : ((H.homeomorph.symm ⟨x, contained member⟩).val : Space) = chart.map x :=
    agrees ⟨x, member⟩
  have placed : D.placed.Places (H.homeomorph.symm ⟨x, contained member⟩).val x :=
    ⟨side, (H.homeomorph.symm ⟨x, contained member⟩).property,
      congrArg Subtype.val (H.homeomorph.apply_symm_apply ⟨x, contained member⟩)⟩
  have same : (H.homeomorph.symm ⟨x, contained member⟩).val =
      (⟨chart.map x, chart.on_surface inside⟩ : frontier P.body) := Subtype.ext folded
  exact same ▸ placed

end SixVertexUnfolding.ConvexPolyhedron.IncidentTriangles
