import SixVertexUnfolding.Geometry.StarFacePlacements
import SixVertexUnfolding.Geometry.DualConnectivity

/-! A connected retained surface gives a connected graph of original
faces meeting at retained edge points. Its spanning tree supplies hinges. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Two distinct whole faces are adjacent when some point of their common edge survives the cuts. -/
def retainedFaceGraph (P : ConvexPolyhedron) (a : frontier P.body) : SimpleGraph P.Face where
  Adj F G := F ≠ G ∧ ∃ b : P.UncutSurface a, (b.val : Space) ∈ F.val ∩ G.val
  symm := by rintro F G ⟨different, b, hF, hG⟩; exact ⟨different.symm, b, hG, hF⟩
  loopless := ⟨fun F h => h.1 rfl⟩

/-- Every retained adjacency is an original edge, since all original vertices have been removed. -/
theorem retainedFaceGraph_original (P : ConvexPolyhedron) (a : frontier P.body) :
    P.retainedFaceGraph a ≤ P.dualGraph := by
  rintro F G ⟨different, b, common⟩
  apply F.shareEdge_of_common_nonvertex G different common
  intro original
  exact b.property ⟨⟨b.val, original⟩, right_mem_segment ℝ _ _⟩

/-- An uncut face interior supplies a retained point of that face. -/
theorem Face.retained_point {P : ConvexPolyhedron} {a : frontier P.body} (F : P.Face)
    (uncut : ∀ (x : Space) (hx : x ∈ F.val),
      P.faceCoordinates F x ∈ interior (P.faceCoordinates F '' F.val) →
      (⟨x, F.subset_frontier hx⟩ : frontier P.body) ∉ P.starCuts a) :
    ∃ b : P.UncutSurface a, (b.val : Space) ∈ F.val := by
  obtain ⟨z, inside⟩ := F.placed_face_interior_nonempty (P.faceCoordinates F) (P.faceCoordinates_rigid F)
  obtain ⟨x, xF, at_z⟩ := interior_subset inside
  exact ⟨⟨⟨x, F.subset_frontier xF⟩, uncut x xF (at_z.symm ▸ inside)⟩, xF⟩

/-- Connectivity of the actual retained surface forces connectivity of its face graph. -/
theorem retainedFaceGraph_connected (P : ConvexPolyhedron) (a : frontier P.body)
    (connected : IsPreconnected (P.starCuts a)ᶜ)
    (meets_faces : ∀ F : P.Face, ∃ b : P.UncutSurface a, (b.val : Space) ∈ F.val) :
    (P.retainedFaceGraph a).Connected := by
  classical
  letI : Nonempty P.Face := P.dualGraph_connected.nonempty
  letI : PreconnectedSpace (P.UncutSurface a) := isPreconnected_iff_preconnectedSpace.mp connected
  let physical : P.UncutSurface a → Space := fun b => b.val
  have continuous_physical : Continuous physical := continuous_subtype_val.comp continuous_subtype_val
  refine ⟨?_⟩
  intro F G
  by_contra disconnected
  let reached := {H : P.Face // (P.retainedFaceGraph a).Reachable F H}
  let unreached := {H : P.Face // ¬ (P.retainedFaceGraph a).Reachable F H}
  let left : Set (P.UncutSurface a) := ⋃ H : reached, physical ⁻¹' H.val.val
  let right : Set (P.UncutSurface a) := ⋃ H : unreached, physical ⁻¹' H.val.val
  have left_closed : IsClosed left := isClosed_iUnion_of_finite
    (fun H => H.val.isClosed.preimage continuous_physical)
  have right_closed : IsClosed right := isClosed_iUnion_of_finite
    (fun H => H.val.isClosed.preimage continuous_physical)
  have cover : univ ⊆ left ∪ right := by
    intro b _
    obtain ⟨H, member⟩ := P.boundary_point_in_face b.val.property
    by_cases reachable : (P.retainedFaceGraph a).Reachable F H
    · exact Or.inl (mem_iUnion.mpr ⟨⟨H, reachable⟩, member⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨H, reachable⟩, member⟩)
  have left_nonempty : (univ ∩ left).Nonempty := by
    obtain ⟨b, member⟩ := meets_faces F
    exact ⟨b, mem_univ _, mem_iUnion.mpr ⟨⟨F, SimpleGraph.Reachable.rfl⟩, member⟩⟩
  have right_nonempty : (univ ∩ right).Nonempty := by
    obtain ⟨b, member⟩ := meets_faces G
    exact ⟨b, mem_univ _, mem_iUnion.mpr ⟨⟨G, disconnected⟩, member⟩⟩
  obtain ⟨b, _, on_left, on_right⟩ := isPreconnected_closed_iff.mp isPreconnected_univ
    left right left_closed right_closed cover left_nonempty right_nonempty
  obtain ⟨A, bA⟩ := mem_iUnion.mp on_left
  obtain ⟨B, bB⟩ := mem_iUnion.mp on_right
  have distinct : A.val ≠ B.val := fun same => B.property (same ▸ A.property)
  have adjacent : (P.retainedFaceGraph a).Adj A.val B.val := ⟨distinct, b, bA, bB⟩
  exact B.property (A.property.trans adjacent.reachable)

end SixVertexUnfolding.ConvexPolyhedron
