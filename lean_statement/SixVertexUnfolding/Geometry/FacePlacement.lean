import SixVertexUnfolding.Geometry.Faces

/-! Each original facet can be placed rigidly in the Euclidean plane. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- Choose orthonormal coordinates on the facet's two-dimensional direction space. -/
theorem exists_rigid_placement :
    ∃ place : Space →ᵃ[ℝ] Plane,
      ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place x) (place y) = dist x y := by
  let D := (affineSpan ℝ F.val).direction
  have dimension : Module.finrank ℝ D = 2 := F.property.1
  let basis : OrthonormalBasis (Fin 2) ℝ D :=
    (stdOrthonormalBasis ℝ D).reindex (finCongr dimension)
  let L : Space →ₗ[ℝ] Plane := basis.repr.toLinearMap.comp D.orthogonalProjection.toLinearMap
  refine ⟨L.toAffineMap, ?_⟩
  intro x hx y hy
  have difference : x - y ∈ D := AffineSubspace.vsub_mem_direction
    (subset_affineSpan ℝ F.val hx) (subset_affineSpan ℝ F.val hy)
  change dist (L x) (L y) = dist x y
  rw [dist_eq_norm, dist_eq_norm, ← L.map_sub]
  change ‖basis.repr (D.orthogonalProjection (x - y))‖ = ‖x - y‖
  rw [basis.repr.norm_map]
  exact D.norm_orthogonalProjection_apply difference

end SixVertexUnfolding.ConvexPolyhedron.Face
