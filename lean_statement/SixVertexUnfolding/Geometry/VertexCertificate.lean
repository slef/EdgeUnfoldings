import SixVertexUnfolding.Geometry.Edges
import SixVertexUnfolding.Geometry.PlacementRigidity
import SixVertexUnfolding.Geometry.Separation

/-!
A construction interface for the later unfolding cases. Rigidity, hinge agreement,
and separation can all be checked at the finitely many original vertices.
The conclusion is the unchanged public unfolding predicate.
-/

namespace SixVertexUnfolding

namespace ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F G : P.Face)

/-- Two affine placements agree on a shared face intersection once they agree at its vertices. -/
theorem joined_of_vertex_agreement (left right : Space →ᵃ[ℝ] Plane)
    (agree : ∀ x ∈ (F.val ∩ G.val) ∩ (P.vertices : Set Space), left x = right x) :
    ∀ x ∈ F.val ∩ G.val, left x = right x := by
  intro x hx
  rw [F.intersection_eq_convexHull_vertices G] at hx
  exact AffineMap.eqOn_affineSpan agree (convexHull_subset_affineSpan _ hx)

end ConvexPolyhedron.Face

/-- A finite certificate for an unfolding of the original polygonal faces.
Every geometric test in the hypotheses concerns original vertices only. -/
theorem hasEdgeUnfolding_of_vertex_certificate
    (P : ConvexPolyhedron)
    (place : P.Face → Space →ᵃ[ℝ] Plane) (hinges : SimpleGraph P.Face)
    (tree : hinges.IsTree) (original_edges : hinges ≤ P.dualGraph)
    (rigid_vertices : ∀ F, ∀ x ∈ F.val ∩ (P.vertices : Set Space),
      ∀ y ∈ F.val ∩ (P.vertices : Set Space), dist (place F x) (place F y) = dist x y)
    (joined_vertices : ∀ F G, hinges.Adj F G →
      ∀ x ∈ (F.val ∩ G.val) ∩ (P.vertices : Set Space), place F x = place G x)
    (separators : ∀ F G, F ≠ G →
      ∃ height : Plane →L[ℝ] ℝ, Function.Surjective height ∧
      ∃ level : ℝ,
        (∀ x ∈ F.val ∩ (P.vertices : Set Space), height (place F x) ≤ level) ∧
        (∀ x ∈ G.val ∩ (P.vertices : Set Space), level ≤ height (place G x))) :
    P.HasEdgeUnfolding := by
  apply hasEdgeUnfolding_of_affine_separators P place hinges tree
  · exact fun _ _ adjacent => original_edges adjacent
  · exact fun F => F.rigid_of_vertex_distances (place F) (rigid_vertices F)
  · exact fun F G adjacent => F.joined_of_vertex_agreement G
      (place F) (place G) (joined_vertices F G adjacent)
  · exact separators

end SixVertexUnfolding
