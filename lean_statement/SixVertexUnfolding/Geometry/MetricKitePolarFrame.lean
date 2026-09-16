import SixVertexUnfolding.Geometry.TriangleFrame
import SixVertexUnfolding.Geometry.CutEdgeReversalMotion
import SixVertexUnfolding.Geometry.PolarArcs

/-! A whole metric kite has symmetric polar coordinates at either root.
No flat chart at that endpoint is needed; it may be an original vertex. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutEdgeMetricModel

open Real Set EuclideanGeometry

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (M : CutEdgeMetricModel T edge)

/-- Place the right root at zero, the left root on the positive axis,
and the two actual source copies at opposite polar angles. -/
theorem exists_reverse_polar_frame :
    let L := dist M.right M.left
    let d := dist M.right M.first
    let θ := angle M.left M.right M.first
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane,
      motion M.right = 0 ∧ motion M.left = L • direction 0 ∧
      motion M.first = d • direction θ ∧ motion M.second = d • direction (-θ) := by
  dsimp only
  have triangle : ¬ Collinear ℝ ({M.right, M.left, M.first} : Set Plane) := by
    simpa only [insert_comm] using M.base_first_noncollinear
  have dp : 0 < dist M.right M.first := dist_pos.mpr (ne₁₃_of_not_collinear triangle)
  have tp := angle_pos_of_not_collinear M.base_first_noncollinear
  have ts := angle_lt_pi_of_not_collinear M.base_first_noncollinear
  obtain ⟨motion, at_right, at_left, at_first⟩ := exists_upper_triangle_frame M.right M.left M.first triangle
  let d := dist M.right M.first
  let L := dist M.right M.left
  let θ := angle M.left M.right M.first
  let p := d • direction θ
  let q := d • direction (-θ)
  have distinct : p ≠ q := by
    intro same
    have angles := polar_angle_eq_of_one_turn d d θ (-θ) dp dp (by dsimp [θ]; linarith)
      (by dsimp [θ]; linarith [pi_pos]) same
    dsimp [θ] at angles
    linarith
  have equal_at_zero : dist p 0 = dist q 0 := by
    dsimp [p, q]
    rw [dist_comm _ 0, dist_comm _ 0, polar_radius d θ dp.le, polar_radius d (-θ) dp.le]
  have equal_at_left : dist p (L • direction 0) = dist q (L • direction 0) := by
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    dsimp [p, q]
    rw [polar_distance_sq, polar_distance_sq]
    simp only [zero_sub, cos_neg, neg_neg]
  have actual_right : dist (motion M.second) 0 = dist p 0 := by
    change dist (motion M.second) 0 = dist (d • direction θ) 0
    rw [← at_right, ← at_first, motion.dist_map, motion.dist_map]
    exact M.right_distances.symm
  have actual_left : dist (motion M.second) (L • direction 0) = dist p (L • direction 0) := by
    change dist (motion M.second) (dist M.right M.left • direction 0) =
      dist (dist M.right M.first • direction (angle M.left M.right M.first))
        (dist M.right M.left • direction 0)
    rw [← at_left, ← at_first, motion.dist_map, motion.dist_map]
    exact M.left_distances.symm
  have base : (0 : Plane) ≠ L • direction 0 := by
    rw [← at_right, ← at_left]
    exact motion.injective.ne M.base_different.symm
  have selected := point_eq_or_eq_of_base_distances 0 (L • direction 0) p q (motion M.second)
    base distinct equal_at_zero equal_at_left actual_right actual_left
  refine ⟨motion, at_right, at_left, at_first, selected.resolve_left ?_⟩
  intro same
  exact M.distinct_sources (motion.injective (at_first.trans same.symm))

end SixVertexUnfolding.ConvexPolyhedron.CutEdgeMetricModel
