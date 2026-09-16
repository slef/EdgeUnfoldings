import SixVertexUnfolding.Geometry.Faces

/-! Straight segments lying in whole original facets. Their endpoints
are geometric points, not newly declared polyhedron vertices. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

structure FaceSegment (P : ConvexPolyhedron) where
  face : P.Face
  first : Space
  last : Space
  first_mem : first ∈ face.val
  last_mem : last ∈ face.val

namespace FaceSegment

variable {P : ConvexPolyhedron} (s : P.FaceSegment)

def points : Set Space := segment ℝ s.first s.last

theorem in_face : s.points ⊆ s.face.val := s.face.convex.segment_subset s.first_mem s.last_mem

theorem convex : Convex ℝ s.points := convex_segment s.first s.last

theorem compact : IsCompact s.points := by
  rw [points, segment_eq_image_lineMap]
  let line : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap s.first s.last
  exact isCompact_Icc.image line.continuous_of_finiteDimensional

end FaceSegment
end SixVertexUnfolding.ConvexPolyhedron
