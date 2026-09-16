import SixVertexUnfolding.Geometry.OctahedralPetalCones
import SixVertexUnfolding.Geometry.OctahedralSelection

/-! The actual apex angles and widened base angles in an opposite-petal comparison. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

noncomputable def petalApexAngle (i : Fin 4) : ℝ :=
  angle (net.patch i).left (net.patch i).apex (net.patch i).right

/-- The middle petal's left base angle, widened by the curvature at that original vertex. -/
noncomputable def widenedLeft (i : Fin 2) : ℝ :=
  angle (net.patch i.castSucc.succ).right (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).apex +
    graph.curvature (fanNeighbor source ((slit + i.castSucc.castSucc) + 1))

noncomputable def widenedRight (i : Fin 2) : ℝ :=
  angle (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).right (net.patch i.castSucc.succ).apex +
    graph.curvature (fanNeighbor source ((slit + i.castSucc.succ) + 1))

theorem petalApexAngle_eq (i : Fin 4) : net.petalApexAngle i = graph.fanAngle source (slit + i) := by
  apply triangle_angle_of_distances
  · simpa only [dist_comm] using (net.patch i).petal_left
  · exact (net.patch i).petal_right
  · exact (net.patch i).hinge_length

theorem petalApexAngle_pos (i : Fin 4) : 0 < net.petalApexAngle i := by
  rw [net.petalApexAngle_eq]
  exact graph.fanAngle_pos _ _

theorem petalApexAngle_lt_pi (i : Fin 4) : net.petalApexAngle i < π := by
  rw [net.petalApexAngle_eq]
  exact graph.fanAngle_lt_pi _ _

theorem sum_petalApexAngle : (∑ i : Fin 4, net.petalApexAngle i) = 2 * π - graph.curvature source := by
  simp only [net.petalApexAngle_eq]
  have rotated : (∑ i : Fin 4, graph.fanAngle source (slit + i)) = ∑ i : Fin 4, graph.fanAngle source i := by
    fin_cases slit <;> simp [Fin.sum_univ_four] <;> ring
  rw [rotated, graph.sum_fanAngle]
  unfold curvature
  ring

theorem widened_angle_sum (i : Fin 2) : net.widenedLeft i + net.widenedRight i =
    π - net.petalApexAngle i.castSucc.succ +
      graph.curvature (fanNeighbor source ((slit + i.castSucc.castSucc) + 1)) +
      graph.curvature (fanNeighbor source ((slit + i.castSucc.succ) + 1)) := by
  have total := angle_add_angle_add_angle_eq_pi (net.patch i.castSucc.succ).apex
    (ne₁₂_of_not_collinear (net.patch i.castSucc.succ).petal_noncollinear).symm
  rw [angle_comm (net.patch i.castSucc.succ).right (net.patch i.castSucc.succ).apex,
    angle_comm (net.patch i.castSucc.succ).apex (net.patch i.castSucc.succ).left] at total
  unfold widenedLeft widenedRight petalApexAngle
  linarith

/-- A high-curvature source bounds each outer apex angle by the widened middle angle. -/
theorem opposite_apex_bounds_of_high_source (i : Fin 2) (high : π ≤ graph.curvature source) :
    net.petalApexAngle i.castSucc.castSucc < net.widenedLeft i + net.widenedRight i ∧
      net.petalApexAngle i.succ.succ < net.widenedLeft i + net.widenedRight i := by
  have total := net.sum_petalApexAngle
  rw [Fin.sum_univ_four] at total
  have positive := net.petalApexAngle_pos
  have left_gap := graph.curvature_pos small_faces (fanNeighbor source ((slit + i.castSucc.castSucc) + 1))
  have right_gap := graph.curvature_pos small_faces (fanNeighbor source ((slit + i.castSucc.succ) + 1))
  rw [net.widened_angle_sum]
  fin_cases i
  · change net.petalApexAngle 0 < π - net.petalApexAngle 1 + _ + _ ∧
      net.petalApexAngle 2 < π - net.petalApexAngle 1 + _ + _
    constructor <;> linarith [positive 0, positive 2, positive 3]
  · change net.petalApexAngle 1 < π - net.petalApexAngle 2 + _ + _ ∧
      net.petalApexAngle 3 < π - net.petalApexAngle 2 + _ + _
    constructor <;> linarith [positive 0, positive 1, positive 3]

/-- If all six curvatures are at most pi, Gauss--Bonnet supplies the same cone angle bounds. -/
theorem opposite_apex_bounds_of_all_low (i : Fin 2) (low : ∀ v, graph.curvature v ≤ π) :
    net.petalApexAngle i.castSucc.castSucc < net.widenedLeft i + net.widenedRight i ∧
      net.petalApexAngle i.succ.succ < net.widenedLeft i + net.widenedRight i := by
  have total := net.sum_petalApexAngle
  rw [Fin.sum_univ_four] at total
  have positive := net.petalApexAngle_pos
  have curvature_total := graph.curvature_poles_equator source
  have rotated : (∑ j : Fin 4, graph.curvature (fanNeighbor source (slit + j))) =
      ∑ j : Fin 4, graph.curvature (fanNeighbor source j) := by
    fin_cases slit <;> simp [Fin.sum_univ_four] <;> ring
  rw [← rotated, Fin.sum_univ_four] at curvature_total
  rw [net.widened_angle_sum]
  fin_cases i
  · change net.petalApexAngle 0 < π - net.petalApexAngle 1 +
        graph.curvature (fanNeighbor source ((slit + 0) + 1)) + graph.curvature (fanNeighbor source ((slit + 1) + 1)) ∧
      net.petalApexAngle 2 < π - net.petalApexAngle 1 +
        graph.curvature (fanNeighbor source ((slit + 0) + 1)) + graph.curvature (fanNeighbor source ((slit + 1) + 1))
    simp only [add_assoc, add_zero, show (1 : Fin 4) + 1 = 2 by decide] at *
    constructor <;> linarith [positive 0, positive 2, positive 3,
      low (opposite source), low (fanNeighbor source slit), low (fanNeighbor source (slit + 3))]
  · change net.petalApexAngle 1 < π - net.petalApexAngle 2 +
        graph.curvature (fanNeighbor source ((slit + 1) + 1)) + graph.curvature (fanNeighbor source ((slit + 2) + 1)) ∧
      net.petalApexAngle 3 < π - net.petalApexAngle 2 +
        graph.curvature (fanNeighbor source ((slit + 1) + 1)) + graph.curvature (fanNeighbor source ((slit + 2) + 1))
    simp only [add_assoc, add_zero, show (1 : Fin 4) + 1 = 2 by decide,
      show (2 : Fin 4) + 1 = 3 by decide] at *
    constructor <;> linarith [positive 0, positive 1, positive 3,
      low (opposite source), low (fanNeighbor source slit), low (fanNeighbor source (slit + 1))]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
