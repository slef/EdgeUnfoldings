import SixVertexUnfolding.Geometry.RetainedHingeAgreement

/-! The geometric star map yields the public edge-unfolding object
when its cuts avoid original face interiors. Rigid faces, nonoverlap,
a spanning tree of original hinges, and whole-edge agreement are derived. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Assemble an actual star development into a net of the original whole faces. -/
theorem edge_unfolding_of_star_development {P : ConvexPolyhedron} {a : frontier P.body}
    (develop : C(P.UncutSurface a, Plane)) (injective : Function.Injective develop)
    (locally_isometric : ∀ b : P.UncutSurface a, ∃ radius > 0,
      ∀ c d : P.UncutSurface a,
        dist (c.val : Space) (b.val : Space) < radius →
        dist (d.val : Space) (b.val : Space) < radius →
        dist (develop c) (develop d) = P.surfaceDist c.val d.val)
    (connected : IsPreconnected (P.starCuts a)ᶜ)
    (uncut : ∀ (F : P.Face) (x : Space) (hx : x ∈ F.val),
      P.faceCoordinates F x ∈ interior (P.faceCoordinates F '' F.val) →
      (⟨x, F.subset_frontier hx⟩ : frontier P.body) ∉ P.starCuts a) : P.HasEdgeUnfolding := by
  obtain ⟨place, rigid, nonoverlap, agrees⟩ := star_face_placements develop injective locally_isometric uncut
  have connected_graph := P.retainedFaceGraph_connected a connected (fun F => F.retained_point (uncut F))
  obtain ⟨hinges, retained, tree⟩ := connected_graph.exists_isTree_le
  exact ⟨{
    place := fun F => place F
    hinges := hinges
    tree := tree
    original_edges := fun F G adjacent => P.retainedFaceGraph_original a (retained adjacent)
    rigid := rigid
    joined := fun F G adjacent => retained_hinge_agreement develop F G (place F) (place G)
      (agrees F) (agrees G) (retained adjacent)
    nonoverlap := nonoverlap }⟩

end SixVertexUnfolding.ConvexPolyhedron
