import SixVertexUnfolding.Geometry.BoundaryCoverage

/-!
The boundary is a sphere topologically, and removing finitely many points leaves
it path connected. Stereographic projection reduces the latter assertion to the
corresponding theorem for the plane.
-/

namespace SixVertexUnfolding

private theorem space_rank_gt_one : 1 < Module.rank ℝ Space := by
  rw [← Module.finrank_eq_rank]
  norm_num [Space]

private theorem plane_rank_gt_one : 1 < Module.rank ℝ Plane := by
  rw [← Module.finrank_eq_rank]
  norm_num [Plane]

/-- A sphere remains path connected after deleting a finite set of its points. -/
theorem sphere_finite_complement_pathConnected
    (missing : Set (Metric.sphere (0 : Space) 1)) (finite_missing : missing.Finite) :
    IsPathConnected missingᶜ := by
  classical
  rcases missing.eq_empty_or_nonempty with empty | ⟨pole, pole_missing⟩
  · rw [empty, Set.compl_empty]
    haveI : PathConnectedSpace (Metric.sphere (0 : Space) 1) :=
      isPathConnected_iff_pathConnectedSpace.mp
        (isPathConnected_sphere space_rank_gt_one 0 zero_le_one)
    exact isPathConnected_univ
  letI : Fact (Module.finrank ℝ Space = 2 + 1) := ⟨by simp [Space]⟩
  let chart := stereographic' 2 pole
  let excluded : Set Plane := chart '' (missing ∩ chart.source)
  have finite_excluded : excluded.Finite := (finite_missing.inter_of_left _).image chart
  have plane_connected := finite_excluded.countable.isPathConnected_compl_of_one_lt_rank
    plane_rank_gt_one
  have inverse_continuous : ContinuousOn chart.symm excludedᶜ :=
    chart.continuousOn_symm.mono (by intro y _; simp [chart])
  have image_eq : chart.symm '' excludedᶜ = missingᶜ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ member
      have y_target : y ∈ chart.target := by simp [chart]
      apply hy
      exact ⟨chart.symm y, ⟨member, chart.map_target y_target⟩, chart.right_inv y_target⟩
    · intro hx
      have x_source : x ∈ chart.source := by
        simp only [chart, stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff]
        intro equal
        exact hx (equal ▸ pole_missing)
      refine ⟨chart x, ?_, chart.left_inv x_source⟩
      rintro ⟨z, ⟨z_missing, z_source⟩, same⟩
      exact hx ((chart.injOn z_source x_source same) ▸ z_missing)
  rw [← image_eq]
  exact plane_connected.image' inverse_continuous

/-- The ambient sphere minus a finite set is path connected. -/
theorem sphere_diff_finite_pathConnected (missing : Set Space) (finite_missing : missing.Finite) :
    IsPathConnected (Metric.sphere (0 : Space) 1 \ missing) := by
  let restricted : Set (Metric.sphere (0 : Space) 1) := Subtype.val ⁻¹' missing
  have restricted_finite : restricted.Finite :=
    finite_missing.preimage Subtype.val_injective.injOn
  have connected := sphere_finite_complement_pathConnected restricted restricted_finite
  have image_eq : Subtype.val '' restrictedᶜ = Metric.sphere (0 : Space) 1 \ missing := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨on_sphere, not_missing⟩
      exact ⟨⟨x, on_sphere⟩, not_missing, rfl⟩
  rw [← image_eq]
  exact connected.image continuous_subtype_val

namespace ConvexPolyhedron

/-- A homeomorphism of three-space sends the polyhedron's entire boundary onto the unit sphere. -/
theorem exists_spherical_homeomorphism (P : ConvexPolyhedron) :
    ∃ h : Space ≃ₜ Space, h '' frontier P.body = Metric.sphere 0 1 := by
  obtain ⟨h, _, _, boundary_eq⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      P.body_convex P.solid P.body_compact.isBounded
  exact ⟨h, boundary_eq⟩

/-- In particular, the boundary stays path connected when the original vertices are removed. -/
theorem frontier_diff_finite_pathConnected (P : ConvexPolyhedron)
    (missing : Set Space) (finite_missing : missing.Finite) :
    IsPathConnected (frontier P.body \ missing) := by
  obtain ⟨h, boundary_eq⟩ := P.exists_spherical_homeomorphism
  have spherical := sphere_diff_finite_pathConnected (h '' missing) (finite_missing.image h)
  have forward_image : h '' (frontier P.body \ missing) =
      Metric.sphere (0 : Space) 1 \ h '' missing := by
    rw [Set.image_diff h.injective, boundary_eq]
  have inverse_image : h.symm '' (Metric.sphere (0 : Space) 1 \ h '' missing) =
      frontier P.body \ missing := by
    rw [← forward_image, Set.image_image]
    simp
  rw [← inverse_image]
  exact spherical.image h.symm.continuous

end ConvexPolyhedron
end SixVertexUnfolding
