import SixVertexUnfolding.Geometry.OctahedralFanFolding
import SixVertexUnfolding.Geometry.ShortPolarSectors

/-! Close to the pole, every ray between the first and last fan directions
lies in one of its actual finite triangles. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- All four outer bases stay away from a common disk about the pole. -/
theorem openingTriangles_small_cones (pole : Fin 6) (slit : Fin 4) :
    ∃ ε > 0, ∀ i : Fin 4, ∀ x ∈ Metric.ball (0 : Plane) ε,
      x ∈ twoRayCone (graph.openingPoint pole slit i.castSucc) (graph.openingPoint pole slit i.succ) →
      x ∈ graph.openingTriangle pole slit i := by
  let base (i : Fin 4) (x : Plane) :=
    det (graph.openingPoint pole slit i.succ - graph.openingPoint pole slit i.castSucc)
      (x - graph.openingPoint pole slit i.castSucc)
  let U : Set Plane := ⋂ i : Fin 4, {x | 0 < base i x}
  have continuous (i : Fin 4) : Continuous (base i) :=
    (detHeight _).continuous.comp (continuous_id.sub continuous_const)
  have openU : IsOpen U := isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous i))
  have zero : (0 : Plane) ∈ U := by
    apply mem_iInter.mpr
    intro i
    have identity : base i 0 =
        det (graph.openingPoint pole slit i.castSucc) (graph.openingPoint pole slit i.succ) := by
      simp only [base, det, PiLp.sub_apply, PiLp.zero_apply]
      ring
    change 0 < base i 0
    rw [identity]
    exact graph.openingTriangle_area_pos pole slit i
  obtain ⟨ε, positive, contained⟩ := Metric.isOpen_iff.mp openU 0 zero
  refine ⟨ε, positive, ?_⟩
  intro i x hx cone
  have sides := (mem_twoRayCone_iff_dets _ _ _ (graph.openingTriangle_area_pos pole slit i)).mp cone
  exact triangle_mem_of_three_halfplanes _ _ x (graph.openingTriangle_area_pos pole slit i)
    sides.1 sides.2 (mem_iInter.mp (contained hx) i).le

/-- Every angle within the opened fan belongs to one of its four consecutive sectors. -/
theorem openingAngle_in_sector (pole : Fin 6) (slit : Fin 4) (θ : ℝ)
    (lower : 0 ≤ θ) (upper : θ ≤ graph.totalAngleAt pole) :
    ∃ i : Fin 4, graph.openingAngle pole slit i.castSucc ≤ θ ∧
      θ ≤ graph.openingAngle pole slit i.succ := by
  by_cases first : θ ≤ graph.openingAngle pole slit 1
  · exact ⟨0, lower, first⟩
  by_cases second : θ ≤ graph.openingAngle pole slit 2
  · exact ⟨1, (lt_of_not_ge first).le, second⟩
  by_cases third : θ ≤ graph.openingAngle pole slit 3
  · exact ⟨2, (lt_of_not_ge second).le, third⟩
  exact ⟨3, (lt_of_not_ge third).le, by
    change θ ≤ graph.openingAngle pole slit 4
    rwa [graph.openingAngle_last]⟩

/-- A common disk contains every sufficiently short radial piece of the full opened fan. -/
theorem openingTriangles_small_rays (pole : Fin 6) (slit : Fin 4) :
    ∃ ε > 0, ∀ r ∈ Icc (0 : ℝ) ε, ∀ θ ∈ Icc (0 : ℝ) (graph.totalAngleAt pole),
      r • direction θ ∈ ⋃ i : Fin 4, graph.openingTriangle pole slit i := by
  obtain ⟨ε, positive, contained⟩ := graph.openingTriangles_small_cones pole slit
  refine ⟨ε / 2, by positivity, ?_⟩
  intro r hr θ hθ
  obtain ⟨i, left, right⟩ := graph.openingAngle_in_sector pole slit θ hθ.1 hθ.2
  apply mem_iUnion.mpr
  refine ⟨i, contained i (r • direction θ) ?_ ?_⟩
  · rw [Metric.mem_ball, dist_comm, polar_radius r θ hr.1]
    linarith [hr.2]
  · apply (mem_twoRayCone_iff_dets _ _ _ (graph.openingTriangle_area_pos pole slit i)).mpr
    change 0 ≤ det (_ • direction _) (r • direction θ) ∧
      0 ≤ det (r • direction θ) (_ • direction _)
    simp only [det_smul_left, det_smul_right, direction_det]
    have step := graph.openingAngle_step pole slit i
    have width := graph.fanAngle_lt_pi pole (slit + i)
    constructor
    · exact mul_nonneg hr.1 (mul_nonneg dist_nonneg
        (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)))
    · exact mul_nonneg dist_nonneg (mul_nonneg hr.1
        (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)))

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
