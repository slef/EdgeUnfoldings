import SixVertexUnfolding.Geometry.FiveFaceFanFolding
import SixVertexUnfolding.Geometry.ShortPolarSectors

/-! A common disk fits inside all five triangles in their respective sectors. -/

namespace SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan

open Set Real

variable {P : ConvexPolyhedron} {pole : P.Vertex} (fan : P.FiveFaceFan pole)

theorem openingTriangles_small_cones (slit : Fin 5) :
    ∃ ε > 0, ∀ i : Fin 5, ∀ x ∈ Metric.ball (0 : Plane) ε,
      x ∈ twoRayCone (fan.openingPoint slit i.castSucc) (fan.openingPoint slit i.succ) →
      x ∈ fan.openingTriangle slit i := by
  let base (i : Fin 5) (x : Plane) :=
    det (fan.openingPoint slit i.succ - fan.openingPoint slit i.castSucc)
      (x - fan.openingPoint slit i.castSucc)
  let U : Set Plane := ⋂ i : Fin 5, {x | 0 < base i x}
  have continuous (i : Fin 5) : Continuous (base i) :=
    (detHeight _).continuous.comp (continuous_id.sub continuous_const)
  have openU : IsOpen U := isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous i))
  have zero : (0 : Plane) ∈ U := by
    apply mem_iInter.mpr
    intro i
    have identity : base i 0 = det (fan.openingPoint slit i.castSucc) (fan.openingPoint slit i.succ) := by
      simp only [base, det, PiLp.sub_apply, PiLp.zero_apply]
      ring
    change 0 < base i 0
    rw [identity]
    exact fan.openingTriangle_area_pos slit i
  obtain ⟨ε, positive, contained⟩ := Metric.isOpen_iff.mp openU 0 zero
  refine ⟨ε, positive, ?_⟩
  intro i x hx cone
  have sides := (mem_twoRayCone_iff_dets _ _ _ (fan.openingTriangle_area_pos slit i)).mp cone
  exact triangle_mem_of_three_halfplanes _ _ x (fan.openingTriangle_area_pos slit i)
    sides.1 sides.2 (mem_iInter.mp (contained hx) i).le

theorem openingAngle_in_sector (slit : Fin 5) (θ : ℝ)
    (lower : 0 ≤ θ) (upper : θ ≤ fan.totalAngle) :
    ∃ i : Fin 5, fan.openingAngle slit i.castSucc ≤ θ ∧ θ ≤ fan.openingAngle slit i.succ := by
  by_cases first : θ ≤ fan.openingAngle slit 1
  · exact ⟨0, lower, first⟩
  by_cases second : θ ≤ fan.openingAngle slit 2
  · exact ⟨1, (lt_of_not_ge first).le, second⟩
  by_cases third : θ ≤ fan.openingAngle slit 3
  · exact ⟨2, (lt_of_not_ge second).le, third⟩
  by_cases fourth : θ ≤ fan.openingAngle slit 4
  · exact ⟨3, (lt_of_not_ge third).le, fourth⟩
  exact ⟨4, (lt_of_not_ge fourth).le, by
    change θ ≤ fan.openingAngle slit 5
    rwa [fan.openingAngle_last]⟩

theorem openingTriangles_small_rays (slit : Fin 5) :
    ∃ ε > 0, ∀ r ∈ Icc (0 : ℝ) ε, ∀ θ ∈ Icc (0 : ℝ) fan.totalAngle,
      r • direction θ ∈ ⋃ i : Fin 5, fan.openingTriangle slit i := by
  obtain ⟨ε, positive, contained⟩ := fan.openingTriangles_small_cones slit
  refine ⟨ε / 2, by positivity, ?_⟩
  intro r hr θ hθ
  obtain ⟨i, left, right⟩ := fan.openingAngle_in_sector slit θ hθ.1 hθ.2
  apply mem_iUnion.mpr
  refine ⟨i, contained i (r • direction θ) ?_ ?_⟩
  · rw [Metric.mem_ball, dist_comm, polar_radius r θ hr.1]
    linarith [hr.2]
  · apply (mem_twoRayCone_iff_dets _ _ _ (fan.openingTriangle_area_pos slit i)).mpr
    change 0 ≤ det (_ • direction _) (r • direction θ) ∧
      0 ≤ det (r • direction θ) (_ • direction _)
    simp only [det_smul_left, det_smul_right, direction_det]
    have step := fan.openingAngle_step slit i
    have width := fan.sectorAngle_lt_pi (slit + i)
    constructor
    · exact mul_nonneg hr.1 (mul_nonneg dist_nonneg
        (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)))
    · exact mul_nonneg dist_nonneg (mul_nonneg hr.1
        (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)))

end SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan
