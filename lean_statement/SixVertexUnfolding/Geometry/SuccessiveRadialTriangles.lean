import SixVertexUnfolding.Geometry.RadialTriangleMotions
import SixVertexUnfolding.Geometry.OutwardTriangle

/-! Join two successive radial triangles along their common endpoint
ray, choosing the side that gives disjoint triangle interiors. -/

namespace SixVertexUnfolding

open Set

/-- Equal-length hinges can be aligned with a chosen outward side. -/
theorem exists_outward_segment_motion (a b c A B C : Plane) (distinct : A ≠ B)
    (same_length : dist a b = dist A B) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, motion a = A ∧ motion b = B ∧
      OppositeHingeSides A B C (motion c) := by
  obtain ⟨align, at_a, at_b⟩ := exists_plane_motion a b A B same_length
  obtain ⟨flip, fixed_a, fixed_b, opposite⟩ := exists_opposite_hinge_motion A B C (align c) distinct
  refine ⟨align.trans flip, ?_, ?_, opposite⟩
  · change flip (align a) = A
    rw [at_a, fixed_a]
  · change flip (align b) = B
    rw [at_b, fixed_b]

namespace ConvexPolyhedron.RadialStripTriangle

variable {P : ConvexPolyhedron}
  {routes other : C(unitInterval, P.BoundaryCurve)} {p l r q u v : Plane}
  (D : RadialStripTriangle routes p l r) (E : RadialStripTriangle other q u v)

/-- Successive edge strips can be aligned along their shared endpoint ray without local overlap. -/
theorem align_successive (same_route : routes 1 = other 0)
    (same_length : dist p r = dist q u)
    (noncollinear : ¬ Collinear ℝ ({q, u, v} : Set Plane)) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, motion p = q ∧ motion r = u ∧
      (∀ x ∈ range (routes 1), ∀ hx : x ∈ range (closedRouteStripMap routes),
        ∀ hy : x ∈ range (closedRouteStripMap other),
          ((D.move motion).homeomorph ⟨x, hx⟩ : Plane) = (E.homeomorph ⟨x, hy⟩ : Plane)) ∧
      Disjoint (interior (convexHull ℝ ({motion p, motion l, motion r} : Set Plane)))
        (interior (convexHull ℝ ({q, u, v} : Set Plane))) := by
  obtain ⟨motion, at_source, at_target, outward⟩ := exists_outward_segment_motion p r l q u v
    (ne₁₂_of_not_collinear noncollinear) same_length
  refine ⟨motion, at_source, at_target, ?_, ?_⟩
  · exact D.agrees_on_shared_route E motion 1 0 same_route at_source (by simpa using at_target)
  · have separated := (opposite_triangles_disjoint q u v (motion l) noncollinear outward).symm
    rw [at_source, at_target]
    convert separated using 1
    congr 2
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto

/-- Nondegenerate successive triangles can be joined with exactly the shared ray as their intersection. -/
theorem align_successive_exact (same_route : routes 1 = other 0)
    (same_length : dist p r = dist q u)
    (first_noncollinear : ¬ Collinear ℝ ({p, l, r} : Set Plane))
    (second_noncollinear : ¬ Collinear ℝ ({q, u, v} : Set Plane)) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, motion p = q ∧ motion r = u ∧
      (∀ x ∈ range (routes 1), ∀ hx : x ∈ range (closedRouteStripMap routes),
        ∀ hy : x ∈ range (closedRouteStripMap other),
          ((D.move motion).homeomorph ⟨x, hx⟩ : Plane) = (E.homeomorph ⟨x, hy⟩ : Plane)) ∧
      convexHull ℝ ({motion p, motion l, motion r} : Set Plane) ∩
        convexHull ℝ ({q, u, v} : Set Plane) = segment ℝ q u := by
  obtain ⟨motion, at_source, at_target, outward⟩ := exists_outward_segment_motion p r l q u v
    (ne₁₂_of_not_collinear second_noncollinear) same_length
  refine ⟨motion, at_source, at_target, ?_, ?_⟩
  · exact D.agrees_on_shared_route E motion 1 0 same_route at_source (by simpa using at_target)
  · have moved : ¬ Collinear ℝ ({q, u, motion l} : Set Plane) := by
      have noncollinear := plane_motion_noncollinear motion p l r first_noncollinear
      rw [at_source, at_target] at noncollinear
      rw [show ({q, u, motion l} : Set Plane) = {q, motion l, u} by
        ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto]
      exact noncollinear
    have weak := (oppositeHingeSides_iff_det q u v (motion l)
      (ne₁₂_of_not_collinear second_noncollinear)).mp outward
    have strict := lt_of_le_of_ne weak (mul_ne_zero
      (det_ne_zero_of_noncollinear q u v second_noncollinear)
      (det_ne_zero_of_noncollinear q u (motion l) moved))
    have intersection := opposite_triangles_intersection q u v (motion l) strict
    rw [at_source, at_target, inter_comm]
    convert intersection using 1
    congr 2
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto

end ConvexPolyhedron.RadialStripTriangle
end SixVertexUnfolding
