import SixVertexUnfolding.Geometry.LocalSourceDistance
import SixVertexUnfolding.Geometry.ShortestTerminalCoordinates

/-! Multiple shortest routes can occur only where two distinct developed
source copies have equal distance in the target face. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  {a b : Space}

include graph small_faces in
/-- Outside source-image ties, a constant-speed shortest route is unique. -/
theorem shortest_routes_agree_of_no_source_ties (first second : P.SurfacePath a b) (different : a ≠ b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (F : P.Face) (unique : ∀ G : P.Face, b ∈ G.val → G = F)
    (no_ties : ∀ p ∈ P.sourceImages a F, ∀ q ∈ P.sourceImages a F, p ≠ q →
      dist p (P.faceCoordinates F b) ≠ dist q (P.faceCoordinates F b)) :
    ∀ t, first.curve t = second.curve t := by
  have source : a ∈ frontier P.body := first.curve.source ▸ first.on_surface 0
  have target : b ∈ frontier P.body := first.curve.target ▸ first.on_surface 1
  obtain ⟨p, _, U, openU, bU, formula⟩ := graph.locally_one_source_image small_faces source target different F unique no_ties
  obtain ⟨V, openV, bV, face⟩ := P.unique_face_neighborhood F unique
  exact first.agree_of_terminal_distance_formula second first_shortest second_shortest first_finite second_finite
    first_speed second_speed
    (graph.shortest_lipschitz_avoids_vertices small_faces first different first_shortest first_finite first_speed)
    F p (U ∩ V) (openU.inter openV) ⟨bU, bV⟩
    (fun _ hx => (face _ ⟨hx.1.2, hx.2⟩).1)
    (fun _ hx => formula _ ⟨hx.1.1, hx.2⟩)

include graph small_faces in
/-- Every pair of distinct shortest routes supplies a tie between distinct planar source copies. -/
theorem distinct_shortest_routes_force_source_tie (first second : P.SurfacePath a b) (different : a ≠ b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (F : P.Face) (unique : ∀ G : P.Face, b ∈ G.val → G = F)
    (distinct_routes : ¬ ∀ t, first.curve t = second.curve t) :
    ∃ p ∈ P.sourceImages a F, ∃ q ∈ P.sourceImages a F, p ≠ q ∧
      dist p (P.faceCoordinates F b) = dist q (P.faceCoordinates F b) := by
  by_contra no_tie
  push Not at no_tie
  exact distinct_routes (graph.shortest_routes_agree_of_no_source_ties small_faces first second different
    first_shortest second_shortest first_finite second_finite first_speed second_speed F unique no_tie)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
