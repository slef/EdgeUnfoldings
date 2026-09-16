import SixVertexUnfolding.Geometry.LocalMinimumDistance
import SixVertexUnfolding.Geometry.MinimumRouteUniqueness
import SixVertexUnfolding.Geometry.MultipleRouteTopology
import SixVertexUnfolding.Geometry.VoronoiDiagram

/-! Within a face, the actual multiple-route locus is locally exactly the
Voronoi boundary of the original target's active sources. This is equality,
not just a cover by candidate bisectors. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Near a distinct target in one face, multiple shortest routes are exactly ties between nearest active sources. -/
theorem local_voronoi_cut_locus (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ ∀ x ∈ V ∩ F.val,
      (x ∈ P.multipleRouteLocus a ↔ P.faceCoordinates F x ∈ voronoiBoundary (P.activeSources a b F)) := by
  obtain ⟨U, openU, bU, minimum⟩ := graph.local_minimum_distance small_faces a b different F unique_face
  obtain ⟨O, openO, bO, face⟩ := P.unique_face_neighborhood F unique_face
  let V := (U ∩ O) ∩ ({(a : Space)}ᶜ : Set Space)
  refine ⟨V, (openU.inter openO).inter isClosed_singleton.isOpen_compl,
    ⟨⟨bU, bO⟩, fun same => different (Subtype.ext same.symm)⟩, ?_⟩
  intro x hx
  let c : frontier P.body := ⟨x, F.subset_frontier hx.2⟩
  have distinct_c : a ≠ c := fun same => hx.1.2 (congrArg Subtype.val same.symm)
  have unique_c := (face x ⟨hx.1.1.2, c.property⟩).2
  have criterion := graph.unique_route_iff_unique_minimum small_faces a c distinct_c F hx.2 unique_c
    (P.activeSources a b F) (graph.activeSources_finite small_faces a b different F unique_face)
    U openU hx.1.1.1 minimum
  have value := minimum x ⟨hx.1.1.1, hx.2⟩
  have ties := mem_voronoiBoundary_iff_multiple_minima (P.activeSources a b F) (P.faceCoordinates F x)
    (P.surfaceDist a x) value.1 value.2
  change (c : Space) ∈ P.multipleRouteLocus a ↔ _
  rw [P.multiple_routes_iff_fiber a c, and_iff_right distinct_c]
  exact criterion.not.trans ties.symm

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
