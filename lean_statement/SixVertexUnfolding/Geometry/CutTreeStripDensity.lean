import SixVertexUnfolding.Geometry.FiniteSegmentDensity
import SixVertexUnfolding.Geometry.RouteSegmentCover
import SixVertexUnfolding.Geometry.CutTreeRadialPartition

/-! The open cut-edge strips occupy a dense part of the actual boundary.
The omitted source, cut set, and finite collection of vertex rays all
lie in a finite collection of straight segments. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Removing the radial partition's exceptional sets leaves a dense surface set. -/
theorem cut_tree_strip_points_dense (a : frontier P.body) (T : P.CutLocusTree a) :
    Dense {b : frontier P.body | b ≠ a ∧ b ∉ P.cutSet a ∧ b ∉ T.vertexRays} := by
  classical
  obtain ⟨segments, finite_segments, exact_segments⟩ := graph.cutSet_finite_segments small_faces a
  letI : Finite segments := finite_segments.to_subtype
  letI : Finite T.vertexRoutes := (graph.cut_tree_vertex_routes_finite small_faces a T).to_subtype
  have covers (f : T.vertexRoutes) :
      ∃ p q : P.Face → Space, ∀ t, ∃ F, (f.val t : Space) ∈ segment ℝ (p F) (q F) := by
    obtain ⟨v, member⟩ := mem_iUnion.mp f.property
    exact P.geodesic_range_segment_cover f.val member.1
  choose p q cover using covers
  let Index := Unit ⊕ (segments ⊕ (T.vertexRoutes × P.Face))
  let left : Index → Space
    | .inl _ => a
    | .inr (.inl s) => s.val.first
    | .inr (.inr x) => p x.1 x.2
  let right : Index → Space
    | .inl _ => a
    | .inr (.inl s) => s.val.last
    | .inr (.inr x) => q x.1 x.2
  apply (P.finite_segments_complement_dense left right).mono
  intro b clear
  refine ⟨?_, ?_, ?_⟩
  · intro same
    apply clear (.inl ())
    simp only [left, right, same, segment_same, mem_singleton_iff]
  · intro cut
    have in_space := (P.mem_cutSetInSpace a b).mpr cut
    rw [exact_segments] at in_space
    obtain ⟨s, in_space⟩ := mem_iUnion.mp in_space
    obtain ⟨member, in_space⟩ := mem_iUnion.mp in_space
    exact clear (.inr (.inl ⟨s, member⟩)) in_space
  · intro ray
    obtain ⟨f, ray⟩ := mem_iUnion.mp ray
    obtain ⟨member, t, at_t⟩ := mem_iUnion.mp ray
    obtain ⟨F, on_segment⟩ := cover ⟨f, member⟩ (interiorTime t)
    apply clear (.inr (.inr (⟨f, member⟩, F)))
    simpa only [at_t] using on_segment

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
