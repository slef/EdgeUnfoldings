import SixVertexUnfolding.Geometry.FacetPlaneInverse
import Mathlib.Geometry.Euclidean.Projection

/-! A rigid placement of an original face extends to a nonexpanding map
of ambient space by first projecting orthogonally onto the face plane. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

open Set EuclideanGeometry

variable {P : ConvexPolyhedron} (F : P.Face)

/-- A face placement has a globally nonexpanding extension with exactly the same face values. -/
theorem exists_nonexpanding_extension (place : Space →ᵃ[ℝ] Plane)
    (rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place x) (place y) = dist x y) :
    ∃ extension : Space → Plane, LipschitzWith 1 extension ∧ EqOn extension place F.val := by
  obtain ⟨a, ha⟩ := F.nonempty
  let plane := affineSpan ℝ F.val
  letI : Nonempty plane := ⟨⟨a, subset_affineSpan ℝ _ ha⟩⟩
  let project : Space → plane := orthogonalProjection plane
  have projection_bound (x y : Space) : dist (project x : Space) (project y : Space) ≤ dist x y := by
    change dist (orthogonalProjection plane x : Space) (orthogonalProjection plane y : Space) ≤ _
    rw [orthogonalProjection_apply', orthogonalProjection_apply']
    change dist ((plane.direction.orthogonalProjection (x - (Classical.arbitrary plane : Space)) : Space) +
      (Classical.arbitrary plane : Space))
      ((plane.direction.orthogonalProjection (y - (Classical.arbitrary plane : Space)) : Space) +
      (Classical.arbitrary plane : Space)) ≤ dist x y
    rw [dist_add_right]
    simpa only [NNReal.coe_one, one_mul, dist_sub_right] using
      plane.direction.lipschitzWith_orthogonalProjection.dist_le_mul
        (x - (Classical.arbitrary plane : Space)) (y - (Classical.arbitrary plane : Space))
  refine ⟨fun x => place (project x), LipschitzWith.of_dist_le_mul (fun x y => ?_), ?_⟩
  · simpa only [NNReal.coe_one, one_mul, F.rigid_on_plane place rigid _ (project x).property _ (project y).property]
      using projection_bound x y
  · intro x hx
    exact congrArg place (orthogonalProjection_eq_self_iff.mpr (subset_affineSpan ℝ _ hx))

end SixVertexUnfolding.ConvexPolyhedron.Face
