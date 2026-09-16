import SixVertexUnfolding.Geometry.SourceImageUniqueness
import SixVertexUnfolding.Geometry.SourceBisectors

/-! The multiple-shortest-route part of the cut locus is contained, in each
open face, in the finite source-bisector arrangement. Tree structure remains open. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Targets distinct from the source that admit two different constant-speed shortest routes. -/
def multipleRouteLocus (P : ConvexPolyhedron) (a : Space) : Set Space :=
  {b | a ≠ b ∧ ∃ first second : P.SurfacePath a b,
    first.IsShortest ∧ second.IsShortest ∧ first.length ≠ ⊤ ∧ second.length ≠ ⊤ ∧
    LipschitzWith first.length.toNNReal first.curve ∧ LipschitzWith second.length.toNNReal second.curve ∧
    ¬ ∀ t, first.curve t = second.curve t}

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  {a b : Space}

include graph small_faces in
/-- Every unique-face point admitting multiple shortest routes lies on a source-copy bisector. -/
theorem multiple_routes_on_source_bisectors (multiple : b ∈ P.multipleRouteLocus a)
    (F : P.Face) (unique : ∀ G : P.Face, b ∈ G.val → G = F) :
    P.faceCoordinates F b ∈ ⋃₀ P.sourceBisectors a F := by
  obtain ⟨different, first, second, first_shortest, second_shortest, first_finite, second_finite,
    first_speed, second_speed, distinct⟩ := multiple
  obtain ⟨p, hp, q, hq, pq, tie⟩ := graph.distinct_shortest_routes_force_source_tie small_faces
    first second different first_shortest second_shortest first_finite second_finite first_speed second_speed F unique distinct
  exact mem_sUnion.mpr ⟨{x | dist p x = dist q x}, ⟨p, hp, q, hq, pq, rfl⟩, tie⟩

include graph small_faces in
/-- A finite set of explicit straight lines covers all multiple-route targets in a face's unique-face region. -/
theorem finite_line_cover_of_multiple_routes (a : Space) (F : P.Face) :
    ∃ lines : Set (Set Plane), lines.Finite ∧
      (∀ line ∈ lines, ∃ normal : Plane, normal ≠ 0 ∧ ∃ c : ℝ, line = {x | inner ℝ normal x = c}) ∧
      ∀ b ∈ P.multipleRouteLocus a, (∀ G : P.Face, b ∈ G.val → G = F) →
        P.faceCoordinates F b ∈ ⋃₀ lines := by
  exact ⟨P.sourceBisectors a F, P.sourceBisectors_finite a F, P.sourceBisector_equation a F,
    fun _ hb unique => graph.multiple_routes_on_source_bisectors small_faces hb F unique⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
