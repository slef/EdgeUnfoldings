import SixVertexUnfolding.Geometry.CircularSourceSides
import SixVertexUnfolding.Geometry.JunctionRayMapAgreement
import SixVertexUnfolding.Geometry.JunctionDevelopedKites

/-! Every source copy in an actual junction fan has an incident
triangle on each side of its retained ray. -/

namespace SixVertexUnfolding.ConvexPolyhedron.JunctionFan

open Set Real

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u : T.vertices} (fan : JunctionFan T u)

theorem exists_source_sides (p : fan.order.chart.sources) :
    ∃ m n : circularGapMidpoints fan.order.angles fan.order.first fan.order.last,
      ∃ side other : Bool,
        (fan.triangles m).motion ((fan.triangles m).apex side) = p.val ∧
        (fan.triangles n).motion ((fan.triangles n).apex other) = p.val ∧
        det (p.val - fan.order.chart.origin)
          ((fan.triangles m).motion (fan.triangles m).model.right - fan.order.chart.origin) < 0 ∧
        0 < det (p.val - fan.order.chart.origin)
          ((fan.triangles n).motion (fan.triangles n).model.right - fan.order.chart.origin) := by
  let θ := fan.order.angles
  let index := fan.order.sites.symm p
  let gap (i : Fin fan.order.chart.sources.ncard) :=
    (circularGapMidpointEquiv θ fan.order.increasing fan.order.bounds fan.order.first fan.order.last fan.order.at_last) i
  have R_positive : 0 < P.surfaceDist a (T.vertexTarget u) := by
    simpa using CutVoronoiChart.tail_radius_pos (T.vertexTarget_different u) (0 : unitInterval)
      (by change (0 : ℝ) < 1; norm_num)
  have at_p : p.val = fan.order.chart.origin + P.surfaceDist a (T.vertexTarget u) • direction (θ index) := by
    simpa only [index, fan.order.sites.apply_symm_apply] using fan.order.position index
  obtain ⟨previous, end_direction, before⟩ := exists_circularGap_before θ fan.order.increasing fan.order.bounds
    fan.order.first fan.order.last fan.order.at_first fan.order.at_last fan.order.two index
  have after := circularGapMidpoint_after θ fan.order.increasing fan.order.bounds
    fan.order.first fan.order.last fan.order.at_last fan.order.two index
  have select_side (i : Fin fan.order.chart.sources.ncard)
      (endpoint : direction (θ index) = direction (θ i) ∨
        direction (θ index) = direction (circularGapEnd θ fan.order.first i)) :
      ∃ side : Bool, (fan.triangles (gap i)).motion ((fan.triangles (gap i)).apex side) = p.val := by
    have pair := fan.gap_source_pair (gap i)
      (circularGapEnd_gap θ fan.order.first fan.order.last i fan.order.at_last) rfl
    have member : p.val ∈ ({(fan.triangles (gap i)).motion (fan.triangles (gap i)).model.first,
        (fan.triangles (gap i)).motion (fan.triangles (gap i)).model.second} : Set Plane) := by
      rw [pair, at_p]
      rcases endpoint with equal | equal
      · exact Or.inl (by rw [equal])
      · exact Or.inr (by rw [equal]; rfl)
    rcases member with first | second
    · exact ⟨false, first.symm⟩
    · exact ⟨true, second.symm⟩
  obtain ⟨side, first_source⟩ := select_side previous (Or.inr end_direction.symm)
  obtain ⟨other, second_source⟩ := select_side index (Or.inl rfl)
  have length_positive (i : Fin fan.order.chart.sources.ncard) :
      0 < dist (u : Space) ((fan.order.neighbors (gap i)).val : Space) := by
    apply dist_pos.mpr
    intro same
    exact (fan.order.neighbors (gap i)).property.ne (Subtype.ext same)
  have area (i : Fin fan.order.chart.sources.ncard) :
      det (p.val - fan.order.chart.origin)
        ((fan.triangles (gap i)).motion (fan.triangles (gap i)).model.right - fan.order.chart.origin) =
      P.surfaceDist a (T.vertexTarget u) *
        (dist (u : Space) ((fan.order.neighbors (gap i)).val : Space) *
          sin ((θ i + circularGapEnd θ fan.order.first i) / 2 - θ index)) := by
    rw [at_p, (fan.triangles (gap i)).at_neighbor, add_sub_cancel_left, add_sub_cancel_left,
      det_smul_left, det_smul_right, direction_det]
    rfl
  refine ⟨gap previous, gap index, side, other, first_source, second_source, ?_, ?_⟩
  · rw [area]
    exact mul_neg_of_pos_of_neg R_positive (mul_neg_of_pos_of_neg (length_positive _) before)
  · rw [area]
    exact mul_pos R_positive (mul_pos (length_positive _) after)

end SixVertexUnfolding.ConvexPolyhedron.JunctionFan
