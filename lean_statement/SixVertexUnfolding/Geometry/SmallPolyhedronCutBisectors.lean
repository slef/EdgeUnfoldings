import SixVertexUnfolding.Geometry.MultipleShortestRoutes
import SixVertexUnfolding.Geometry.SmallPolyhedronSourceUniqueness
import SixVertexUnfolding.Geometry.SourceBisectors

/-! The multiple-shortest-route part of the cut locus is contained, in each
open face, in the finite source-bisector arrangement. This covers face
interiors; the complete cut-tree construction is separate. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  {a b : Space}

include size small_faces in
/-- Every unique-face point admitting multiple shortest routes lies on a source-copy bisector. -/
theorem small_multiple_routes_on_source_bisectors (multiple : b ∈ P.multipleRouteLocus a)
    (F : P.Face) (unique : ∀ G : P.Face, b ∈ G.val → G = F) :
    P.faceCoordinates F b ∈ ⋃₀ P.sourceBisectors a F := by
  obtain ⟨different, first, second, first_shortest, second_shortest, first_finite, second_finite,
    first_speed, second_speed, distinct⟩ := multiple
  obtain ⟨p, hp, q, hq, pq, tie⟩ := small_distinct_shortest_routes_force_source_tie size small_faces
    first second different first_shortest second_shortest first_finite second_finite first_speed second_speed F unique distinct
  exact mem_sUnion.mpr ⟨{x | dist p x = dist q x}, ⟨p, hp, q, hq, pq, rfl⟩, tie⟩

include size small_faces in
/-- A finite set of explicit straight lines covers all multiple-route targets in a face's unique-face region. -/
theorem small_finite_line_cover_of_multiple_routes (a : Space) (F : P.Face) :
    ∃ lines : Set (Set Plane), lines.Finite ∧
      (∀ line ∈ lines, ∃ normal : Plane, normal ≠ 0 ∧ ∃ c : ℝ, line = {x | inner ℝ normal x = c}) ∧
      ∀ b ∈ P.multipleRouteLocus a, (∀ G : P.Face, b ∈ G.val → G = F) →
        P.faceCoordinates F b ∈ ⋃₀ lines := by
  exact ⟨P.sourceBisectors a F, P.sourceBisectors_finite a F, P.sourceBisector_equation a F,
    fun _ hb unique => small_multiple_routes_on_source_bisectors size small_faces hb F unique⟩

end SixVertexUnfolding.ConvexPolyhedron
