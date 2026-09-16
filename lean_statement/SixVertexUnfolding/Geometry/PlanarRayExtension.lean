import SixVertexUnfolding.Geometry.ShortestRayEndpoints

/-! A single planar source-distance formula lets a shortest ray continue
strictly farther through every ordinary interior point of its chart. -/

namespace SixVertexUnfolding

open Set

/-- Every neighborhood contains a point strictly farther along the ray from `source` through `z`. -/
theorem planar_ray_extension (source z : Plane) (different : source ≠ z)
    (U : Set Plane) (openU : IsOpen U) (zU : z ∈ U) :
    ∃ w ∈ U, w ≠ z ∧ dist source w = dist source z + dist z w := by
  let ray : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap source z
  have at_one : ray 1 = z := AffineMap.lineMap_apply_one source z
  have one_in : (1 : ℝ) ∈ ray ⁻¹' U := by change ray 1 ∈ U; rwa [at_one]
  obtain ⟨ε, positive, contained⟩ := Metric.isOpen_iff.mp
    (openU.preimage ray.continuous_of_finiteDimensional) 1 one_in
  let t : ℝ := 1 + ε / 2
  have after : 1 < t := by dsimp [t]; linarith
  have near : t ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr after)]
    dsimp [t]
    linarith
  have from_source : dist source (ray t) = t * dist source z := by
    change dist source (AffineMap.lineMap source z t) = _
    rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < t)]
  have from_z : dist z (ray t) = (t - 1) * dist source z := by
    change dist z (AffineMap.lineMap source z t) = _
    rw [dist_comm, dist_lineMap_right, Real.norm_eq_abs,
      abs_of_neg (by linarith : 1 - t < 0)]
    ring
  refine ⟨ray t, contained near, ?_, ?_⟩
  · intro equal
    have pos := dist_pos.mpr different
    rw [equal, dist_self] at from_z
    nlinarith
  · rw [from_source, from_z]
    ring

namespace ConvexPolyhedron

/-- A local planar source formula gives a strict intrinsic shortest extension. -/
theorem shortest_extension_of_planar_formula (P : ConvexPolyhedron) (a b : frontier P.body)
    (different : a ≠ b) (source origin : Plane) (map : Plane → Space)
    (U : Set Plane) (openU : IsOpen U) (originU : origin ∈ U)
    (at_origin : map origin = b) (on_surface : MapsTo map U (frontier P.body))
    (metric : ∀ x ∈ U, P.surfaceDist b (map x) = dist origin x)
    (formula : ∀ x ∈ U, P.surfaceDist a (map x) = dist source x) :
    ∃ c ∈ P.shortestExtensions a b, c ≠ b := by
  have positive : 0 < P.surfaceDist a b := lt_of_le_of_ne (P.surfaceDist_nonneg a b)
    (fun zero => different (Subtype.ext ((P.surfaceDist_eq_zero_iff a.property b.property).mp zero.symm)))
  have source_ne : source ≠ origin := by
    intro same
    have value := formula origin originU
    rw [at_origin, same, dist_self] at value
    linarith
  obtain ⟨w, wU, different_w, farther⟩ := planar_ray_extension source origin source_ne U openU originU
  refine ⟨⟨map w, on_surface wU⟩, ?_, ?_⟩
  · change P.surfaceDist a (map w) = P.surfaceDist a b + P.surfaceDist b (map w)
    rw [formula w wU, metric w wU, ← at_origin, formula origin originU]
    exact farther
  · intro same
    have value := metric w wU
    have equal : map w = (b : Space) := congrArg Subtype.val same
    rw [equal, P.surfaceDist_self b.property] at value
    exact different_w (dist_eq_zero.mp value.symm).symm

end ConvexPolyhedron
end SixVertexUnfolding
