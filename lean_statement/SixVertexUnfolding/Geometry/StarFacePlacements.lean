import SixVertexUnfolding.Geometry.UncutFaceNonoverlap

/-! Conversion from an actual injective local isometry to whole-face
placements, whenever the cuts avoid face interiors. This applies to any
polyhedron once its geometric development has been constructed; selecting
a connected family of retained original hinges remains separate. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- An injective locally isometric star map determines rigid, nonoverlapping original faces. -/
theorem star_face_placements {P : ConvexPolyhedron} {a : frontier P.body}
    (develop : C(P.UncutSurface a, Plane)) (injective : Function.Injective develop)
    (locally_isometric : ∀ b : P.UncutSurface a, ∃ radius > 0,
      ∀ c d : P.UncutSurface a,
        dist (c.val : Space) (b.val : Space) < radius →
        dist (d.val : Space) (b.val : Space) < radius →
        dist (develop c) (develop d) = P.surfaceDist c.val d.val)
    (uncut : ∀ (F : P.Face) (x : Space) (hx : x ∈ F.val),
      P.faceCoordinates F x ∈ interior (P.faceCoordinates F '' F.val) →
      (⟨x, F.subset_frontier hx⟩ : frontier P.body) ∉ P.starCuts a) :
    ∃ place : P.Face → Space →ᵃ[ℝ] Plane,
      (∀ F, ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place F x) (place F y) = dist x y) ∧
      (∀ F G, F ≠ G → Disjoint (interior (place F '' F.val)) (interior (place G '' G.val))) ∧
      ∀ F, ∀ b : P.UncutSurface a, (b.val : Space) ∈ F.val → place F b.val = develop b := by
  classical
  have each_face (F : P.Face) : ∃ place : Space →ᵃ[ℝ] Plane,
      (∀ x ∈ F.val, ∀ y ∈ F.val, dist (place x) (place y) = dist x y) ∧
      ∀ b : P.UncutSurface a, (b.val : Space) ∈ F.val → place b.val = develop b := by
    obtain ⟨place, rigid, agrees⟩ := uncut_face_rigid_placement develop locally_isometric F (uncut F)
    exact ⟨place, rigid, F.agrees_on_retained_face develop place agrees⟩
  choose place rigid agrees using each_face
  refine ⟨place, rigid, ?_, agrees⟩
  intro F G different
  exact uncut_face_placements_nonoverlap develop injective F G different
    (place F) (place G) (rigid F) (rigid G) (uncut F) (uncut G) (agrees F) (agrees G)

end SixVertexUnfolding.ConvexPolyhedron
