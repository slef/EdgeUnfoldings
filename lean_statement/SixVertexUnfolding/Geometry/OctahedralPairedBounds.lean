import SixVertexUnfolding.Geometry.OctahedralOppositeAngles

/-! The paired-pole rule supplies the wider apex-cone bounds from actual spatial link inequalities. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem petal_base_angle_sum (i : Fin 4) :
    angle (net.patch i).right (net.patch i).left (net.patch i).apex +
      angle (net.patch i).left (net.patch i).right (net.patch i).apex = π - net.petalApexAngle i := by
  have total := angle_add_angle_add_angle_eq_pi (net.patch i).apex
    (ne₁₂_of_not_collinear (net.patch i).petal_noncollinear).symm
  rw [angle_comm (net.patch i).right (net.patch i).apex,
    angle_comm (net.patch i).apex (net.patch i).left] at total
  unfold petalApexAngle
  linarith

theorem petal_left_link (i : Fin 4) :
    2 * angle (net.patch i).right (net.patch i).left (net.patch i).apex <
      2 * π - graph.curvature (fanNeighbor source (slit + i)) := by
  rw [(net.patch i).petal_angle_at_left]
  apply graph.vertex_angle_lt_half_deficit small_faces
  · exact (by decide : ∀ s j, fanNeighbor s (j + 1) ≠ fanNeighbor s j) source (slit + i)
  · exact (fanNeighbor_ne_source source (slit + i)).symm
  · exact (by decide : ∀ s j, fanNeighbor s (j + 1) ≠ opposite (fanNeighbor s j)) source (slit + i)

theorem petal_right_link (i : Fin 4) :
    2 * angle (net.patch i).left (net.patch i).right (net.patch i).apex <
      2 * π - graph.curvature (fanNeighbor source ((slit + i) + 1)) := by
  rw [angle_comm, (net.patch i).petal_angle_at_right]
  apply graph.vertex_angle_lt_half_deficit small_faces
  · exact (fanNeighbor_ne_source source ((slit + i) + 1)).symm
  · exact (by decide : ∀ s j, fanNeighbor s j ≠ fanNeighbor s (j + 1)) source (slit + i)
  · exact (by decide : ∀ s j, s ≠ opposite (fanNeighbor s (j + 1))) source (slit + i)

theorem opposite_outer_angle_sum (i : Fin 2) :
    net.petalApexAngle i.castSucc.castSucc + net.petalApexAngle i.succ.succ <
      π + (net.widenedLeft i + net.widenedRight i) := by
  have total := net.sum_petalApexAngle
  rw [Fin.sum_univ_four] at total
  have positive := net.petalApexAngle_pos
  have source_pos := graph.curvature_pos small_faces source
  have left_gap := graph.curvature_pos small_faces (fanNeighbor source ((slit + i.castSucc.castSucc) + 1))
  have right_gap := graph.curvature_pos small_faces (fanNeighbor source ((slit + i.castSucc.succ) + 1))
  rw [net.widened_angle_sum]
  fin_cases i
  · change net.petalApexAngle 0 + net.petalApexAngle 2 < π + (π - net.petalApexAngle 1 + _ + _)
    linarith [positive 3]
  · change net.petalApexAngle 1 + net.petalApexAngle 3 < π + (π - net.petalApexAngle 2 + _ + _)
    linarith [positive 0]

/-- Choosing the sharper endpoint of any opposite pair gives both wider Case A angle bounds. -/
theorem opposite_wider_apex_bounds (i : Fin 2)
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source) :
    net.petalApexAngle i.castSucc.castSucc < (π + (net.widenedLeft i + net.widenedRight i)) / 2 ∧
      net.petalApexAngle i.succ.succ < (π + (net.widenedLeft i + net.widenedRight i)) / 2 := by
  have total := net.sum_petalApexAngle
  rw [Fin.sum_univ_four] at total
  have curvature_total := graph.curvature_poles_equator source
  have rotated : (∑ j : Fin 4, graph.curvature (fanNeighbor source (slit + j))) =
      ∑ j : Fin 4, graph.curvature (fanNeighbor source j) := by
    fin_cases slit <;> simp [Fin.sum_univ_four] <;> ring
  rw [← rotated, Fin.sum_univ_four] at curvature_total
  rw [net.widened_angle_sum]
  fin_cases i
  · have triangle := net.petal_base_angle_sum 3
    have left_link := net.petal_left_link 3
    have right_link := net.petal_right_link 3
    simp only [add_assoc, show (3 : Fin 4) + 1 = 0 by decide, add_zero] at right_link curvature_total
    have bounds := PairedPoles.wider_caseA_bounds
      (K := graph.curvature (fanNeighbor source (slit + 1)) + graph.curvature (fanNeighbor source (slit + 2)))
      (ka := graph.curvature (fanNeighbor source (slit + 3))) (kb := graph.curvature (fanNeighbor source slit))
      (ξ := angle (net.patch 3).right (net.patch 3).left (net.patch 3).apex)
      (ζ := angle (net.patch 3).left (net.patch 3).right (net.patch 3).apex)
      (by linarith : net.petalApexAngle 3 + net.petalApexAngle 0 + net.petalApexAngle 1 + net.petalApexAngle 2 = 2 * π - graph.curvature source)
      triangle (by linarith) source_order (net.petalApexAngle_pos 0) (net.petalApexAngle_pos 1) (net.petalApexAngle_pos 2)
      (by unfold PairedPoles.linkSlack; linarith) (by unfold PairedPoles.linkSlack; linarith)
    change net.petalApexAngle 0 < (π + (π - net.petalApexAngle 1 +
        graph.curvature (fanNeighbor source ((slit + 0) + 1)) + graph.curvature (fanNeighbor source ((slit + 1) + 1)))) / 2 ∧
      net.petalApexAngle 2 < (π + (π - net.petalApexAngle 1 +
        graph.curvature (fanNeighbor source ((slit + 0) + 1)) + graph.curvature (fanNeighbor source ((slit + 1) + 1)))) / 2
    simp only [add_assoc, add_zero, show (1 : Fin 4) + 1 = 2 by decide] at *
    constructor <;> linarith [bounds.1, bounds.2]
  · have triangle := net.petal_base_angle_sum 0
    have left_link := net.petal_left_link 0
    have right_link := net.petal_right_link 0
    simp only [add_zero] at left_link right_link curvature_total
    have bounds := PairedPoles.wider_caseA_bounds
      (K := graph.curvature (fanNeighbor source (slit + 2)) + graph.curvature (fanNeighbor source (slit + 3)))
      (ka := graph.curvature (fanNeighbor source slit)) (kb := graph.curvature (fanNeighbor source (slit + 1)))
      (ξ := angle (net.patch 0).right (net.patch 0).left (net.patch 0).apex)
      (ζ := angle (net.patch 0).left (net.patch 0).right (net.patch 0).apex)
      (by linarith : net.petalApexAngle 0 + net.petalApexAngle 1 + net.petalApexAngle 2 + net.petalApexAngle 3 = 2 * π - graph.curvature source)
      triangle (by linarith) source_order (net.petalApexAngle_pos 1) (net.petalApexAngle_pos 2) (net.petalApexAngle_pos 3)
      (by unfold PairedPoles.linkSlack; linarith) (by unfold PairedPoles.linkSlack; linarith)
    change net.petalApexAngle 1 < (π + (π - net.petalApexAngle 2 +
        graph.curvature (fanNeighbor source ((slit + 1) + 1)) + graph.curvature (fanNeighbor source ((slit + 2) + 1)))) / 2 ∧
      net.petalApexAngle 3 < (π + (π - net.petalApexAngle 2 +
        graph.curvature (fanNeighbor source ((slit + 1) + 1)) + graph.curvature (fanNeighbor source ((slit + 2) + 1)))) / 2
    simp only [add_assoc, show (1 : Fin 4) + 1 = 2 by decide, show (2 : Fin 4) + 1 = 3 by decide] at *
    constructor <;> linarith [bounds.1, bounds.2]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
