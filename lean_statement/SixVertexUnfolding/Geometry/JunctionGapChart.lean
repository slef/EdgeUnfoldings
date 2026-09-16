import SixVertexUnfolding.Geometry.IncidentSectorChart
import SixVertexUnfolding.Geometry.JunctionDevelopedKites

/-! The two labelled sides of every actual angular gap together
cover that entire gap near the junction, with the correct chart map. -/

namespace SixVertexUnfolding.ConvexPolyhedron.JunctionFan

open Set Real

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u : T.vertices} (fan : JunctionFan T u)

theorem exists_gap_chart_sector
    (m : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    {α β : ℝ} (gap : IsCircularGap fan.order.angles fan.order.first fan.order.last α β)
    (midpoint : (m : ℝ) = (α + β) / 2) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε, ∀ φ ∈ Icc α β,
      let x := fan.order.chart.origin + ρ • direction φ
      ∃ inside : x ∈ fan.order.chart.domain,
        (fan.triangles m).placed.Places ⟨fan.order.chart.map x, fan.order.chart.on_surface inside⟩ x := by
  let D := fan.triangles m
  let C := fan.order.chart
  let R := P.surfaceDist a (T.vertexTarget u)
  obtain ⟨ordered, width, _, _, _, _, _⟩ := circular_gap_spec
    fan.order.sites fan.order.angles fan.order.increasing fan.order.bounds C.origin R fan.order.position
    fan.order.first fan.order.last fan.order.at_first fan.order.at_last fan.order.two gap
  have radius_positive : 0 < R := by
    simpa using CutVoronoiChart.tail_radius_pos (T.vertexTarget_different u) (0 : unitInterval)
      (by change (0 : ℝ) < 1; norm_num)
  have pair := fan.gap_source_pair m gap midpoint
  have side_at (θ : ℝ) (at_end : θ = α ∨ θ = β) :
      ∃ side : Bool, D.motion (D.apex side) = C.origin + R • direction θ := by
    have member : C.origin + R • direction θ ∈
        ({D.motion D.model.first, D.motion D.model.second} : Set Plane) := by
      rw [pair]
      rcases at_end with rfl | rfl <;> simp [C, R]
    rcases member with first | second
    · exact ⟨false, first.symm⟩
    · exact ⟨true, second.symm⟩
  obtain ⟨left_side, left_position⟩ := side_at α (Or.inl rfl)
  obtain ⟨right_side, right_position⟩ := side_at β (Or.inr rfl)
  have left_before : α < (m : ℝ) := by rw [midpoint]; linarith
  have right_after : (m : ℝ) < β := by rw [midpoint]; linarith
  obtain ⟨ε, ep, left_sector⟩ := D.exists_chart_sector left_side fan.order.radius_positive
    (fan.order.rays m) radius_positive left_position left_before.ne
    (by rw [abs_of_pos (sub_pos.mpr left_before), midpoint]; linarith)
  obtain ⟨δ, dp, right_sector⟩ := D.exists_chart_sector right_side fan.order.radius_positive
    (fan.order.rays m) radius_positive right_position right_after.ne'
    (by rw [abs_of_neg (sub_neg.mpr right_after), midpoint]; linarith)
  refine ⟨min ε δ, lt_min ep dp, ?_⟩
  intro ρ hr φ hφ
  by_cases first_half : φ ≤ (m : ℝ)
  · apply left_sector ρ ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩ φ
    simpa only [min_eq_left left_before.le, max_eq_right left_before.le] using ⟨hφ.1, first_half⟩
  · apply right_sector ρ ⟨hr.1, hr.2.trans_le (min_le_right _ _)⟩ φ
    simpa only [min_eq_right right_after.le, max_eq_left right_after.le] using ⟨(lt_of_not_ge first_half).le, hφ.2⟩

end SixVertexUnfolding.ConvexPolyhedron.JunctionFan
