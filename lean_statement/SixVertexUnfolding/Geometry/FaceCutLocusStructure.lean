import SixVertexUnfolding.Geometry.LocalVoronoiCutLocus
import SixVertexUnfolding.Geometry.ActiveSourceRoutes
import SixVertexUnfolding.Geometry.VoronoiJunctions

/-! Within each original face, two-route points have ordinary bisector
neighborhoods and points with at least three routes form a finite set. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Exactly two shortest routes give a whole local bisector, with no omitted subpieces. -/
theorem two_route_local_bisector (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F)
    (two : Nat.card (P.geodesicFiber a b) = 2) :
    ∃ p ∈ P.activeSources a b F, ∃ q ∈ P.activeSources a b F, p ≠ q ∧
      ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ ∀ x ∈ V ∩ F.val,
        (x ∈ P.multipleRouteLocus a ↔ dist p (P.faceCoordinates F x) = dist q (P.faceCoordinates F x)) := by
  have cardinal := (graph.activeSources_ncard small_faces a b different F unique_face).trans two
  obtain ⟨p, q, distinct, pair⟩ := ncard_eq_two.mp cardinal
  obtain ⟨V, openV, bV, diagram⟩ := graph.local_voronoi_cut_locus small_faces a b different F unique_face
  refine ⟨p, by rw [pair]; simp, q, by rw [pair]; simp, distinct, V, openV, bV, ?_⟩
  intro x hx
  rw [diagram x hx, pair, voronoiBoundary_pair p q distinct]
  rfl

include graph small_faces in
/-- Only finitely many interior-face targets admit three or more shortest routes. -/
theorem face_junctions_finite (a : frontier P.body) (F : P.Face) :
    {b : frontier P.body | a ≠ b ∧ (∀ G : P.Face, (b : Space) ∈ G.val → G = F) ∧
      2 < Nat.card (P.geodesicFiber a b)}.Finite := by
  let junctions : Set (frontier P.body) := {b | a ≠ b ∧
    (∀ G : P.Face, (b : Space) ∈ G.val → G = F) ∧ 2 < Nat.card (P.geodesicFiber a b)}
  have image_finite : ((fun b : frontier P.body => P.faceCoordinates F b) '' junctions).Finite := by
    apply (finite_three_site_centers (P.sourceImages a F) (P.sourceImages_finite a F)).subset
    rintro _ ⟨b, hb, rfl⟩
    have count : 2 < (P.activeSources a b F).ncard := by
      rw [graph.activeSources_ncard small_faces a b hb.1 F hb.2.1]
      exact hb.2.2
    obtain ⟨p, hp, q, hq, r, hr, pq, pr, qr⟩ :=
      (two_lt_ncard (graph.activeSources_finite small_faces a b hb.1 F hb.2.1)).mp count
    have subset := graph.activeSources_subset small_faces a b hb.1 F hb.2.1
    have pvalue := P.activeSource_distance a b F p hp
    exact ⟨p, subset hp, q, subset hq, r, subset hr, pq, pr, qr,
      pvalue.symm.trans (P.activeSource_distance a b F q hq),
      pvalue.symm.trans (P.activeSource_distance a b F r hr)⟩
  apply image_finite.of_finite_image
  intro b hb c hc same
  have in_face (x : frontier P.body) (hx : x ∈ junctions) : (x : Space) ∈ F.val := by
    obtain ⟨G, member⟩ := P.boundary_point_in_face x.property
    simpa only [hx.2.1 G member] using member
  apply Subtype.ext
  apply dist_eq_zero.mp
  change P.faceCoordinates F b = P.faceCoordinates F c at same
  rw [← P.faceCoordinates_rigid F _ (in_face b hb) _ (in_face c hc), same, dist_self]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
