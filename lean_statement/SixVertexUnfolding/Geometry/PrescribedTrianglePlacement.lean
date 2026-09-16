import SixVertexUnfolding.Geometry.FacePlacement
import SixVertexUnfolding.Geometry.FacetCoordinates
import SixVertexUnfolding.Geometry.PlacementRigidity
import SixVertexUnfolding.Geometry.TriangleNondegeneracy
import SixVertexUnfolding.Geometry.TriangleTopology

/-! Place an entire original facet by prescribing a congruent triangle on it. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- A congruent copy of three original facet vertices determines a rigid placement of the whole facet. -/
theorem exists_placement_at_triangle (a b c : P.Vertex)
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (aF : (a : Space) ∈ F.val) (bF : (b : Space) ∈ F.val) (cF : (c : Space) ∈ F.val)
    (A B C : Plane) (AB : dist A B = dist (a : Space) b)
    (AC : dist A C = dist (a : Space) c) (BC : dist B C = dist (b : Space) c) :
    ∃ place : Space →ᵃ[ℝ] Plane,
      place a = A ∧ place b = B ∧ place c = C ∧
      ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place x) (place y) = dist x y := by
  obtain ⟨canonical, rigid⟩ := F.exists_rigid_placement
  have noncollinear := P.placed_triangle_noncollinear a b c ab ac bc
    (canonical a) (canonical b) (canonical c) (rigid a aF b bF) (rigid a aF c cF) (rigid b bF c cF)
  let basis : AffineBasis (Fin 3) ℝ Plane := {
    toFun := ![canonical a, canonical b, canonical c]
    ind' := affineIndependent_iff_not_collinear_set.mpr noncollinear
    tot' := by
      have points : Set.range ![canonical a, canonical b, canonical c] =
          ({canonical a, canonical b, canonical c} : Set Plane) := by
        ext x
        simp [Matrix.range_cons, Matrix.range_empty]
        tauto
      rw [points]
      exact planar_triangle_spans _ _ _ noncollinear
  }
  let target : Fin 3 → Plane := ![A, B, C]
  let replace : Plane →ᵃ[ℝ] Plane := (Fintype.linearCombination ℝ target).toAffineMap.comp basis.coords
  have sends (i : Fin 3) : replace (basis i) = target i := by
    simp [replace, Fintype.linearCombination_apply, AffineBasis.coord_apply]
  let place := replace.comp canonical
  have at_a : place a = A := sends 0
  have at_b : place b = B := sends 1
  have at_c : place c = C := sends 2
  refine ⟨place, at_a, at_b, at_c, ?_⟩
  have spatial : ¬ Collinear ℝ ({(a : Space), (b : Space), (c : Space)} : Set Space) :=
    P.no_three_collinear_vertices a.property b.property c.property
      (fun same => ab (Subtype.ext same)) (fun same => ac (Subtype.ext same)) (fun same => bc (Subtype.ext same))
  have plane_eq := F.triangle_spans_plane a b c aF bF cF spatial
  have triangle_rigid := affine_rigid_on_span_of_distances place
    ({(a : Space), (b : Space), (c : Space)} : Set Space) (by simp) (by
      rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) <;>
        simp [at_a, at_b, at_c, AB, AC, BC, dist_comm])
  intro x hx y hy
  apply triangle_rigid
  · rw [plane_eq]
    exact subset_affineSpan ℝ F.val hx
  · rw [plane_eq]
    exact subset_affineSpan ℝ F.val hy

end SixVertexUnfolding.ConvexPolyhedron.Face
