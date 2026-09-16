import SixVertexUnfolding.Geometry.PyramidFaces
import SixVertexUnfolding.Geometry.TrianglePetal

/-! Apply the outward-triangle construction to each original side of a pyramid. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Pyramid

/-- A rigid base placement extends to an outward side triangle with all required comparisons. -/
theorem exists_petal {P : ConvexPolyhedron} (p : P.Pyramid) (F : P.Face) (side : F ≠ p.base)
    (left : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ p.base.val, ∀ y ∈ p.base.val, dist (left x) (left y) = dist x y) :
    ∃ right : Space →ᵃ[ℝ] Plane,
      (∀ x ∈ F.val, ∀ y ∈ F.val, dist (right x) (right y) = dist x y) ∧
      (∀ x : P.Vertex, (x : Space) ∈ F.val → (x : Space) ∈ p.base.val → right x = left x) ∧
      Disjoint (interior (left '' p.base.val)) (interior (right '' F.val)) ∧
      (∀ x : P.Vertex, (x : Space) ∈ p.base.val → (x : Space) ∉ F.val →
        dist (x : Space) p.apex < dist (left x) (right p.apex)) := by
  obtain ⟨a, b, ab, aB, bB, _, vertices⟩ := p.side_vertices F side
  exact p.base.exists_triangle_petal F a b p.apex ab aB bB vertices p.apex_outside left left_rigid

end SixVertexUnfolding.ConvexPolyhedron.Pyramid
