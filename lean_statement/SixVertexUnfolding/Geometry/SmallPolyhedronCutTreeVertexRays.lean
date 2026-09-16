import SixVertexUnfolding.Geometry.CutTreeVertexRays
import SixVertexUnfolding.Geometry.SmallPolyhedronCutRayCoordinates
import SixVertexUnfolding.Geometry.SmallPolyhedronCutRetraction
import SixVertexUnfolding.Geometry.SmallPolyhedronShortestRoutes
import SixVertexUnfolding.Geometry.SmallPolyhedronTerminalRays

/-! The finite collection of shortest rays from the source to cut-tree
vertices supplies the boundaries between the open-edge strips.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
theorem small_cut_tree_vertex_routes_finite (a : frontier P.body) (T : P.CutLocusTree a) :
    T.vertexRoutes.Finite := by
  letI : Finite T.vertices := T.finite_vertices
  exact finite_iUnion (fun v => small_geodesicFiber_finite size small_faces a (T.vertexTarget v)
    (T.vertexTarget_different v))

include size small_faces in
/-- Distinct terminal routes have disjoint open rays. -/
theorem small_cut_tree_vertex_rays_disjoint (a : frontier P.body) (T : P.CutLocusTree a) :
    T.vertexRoutes.PairwiseDisjoint openRay := by
  intro f hf g hg different
  obtain ⟨u, hf⟩ := mem_iUnion.mp hf
  obtain ⟨v, hg⟩ := mem_iUnion.mp hg
  apply disjoint_left.mpr
  rintro b ⟨s, hs⟩ ⟨t, ht⟩
  exact different (small_cut_rays_meeting size small_faces a _ _ (T.vertexTarget_cut u)
    (T.vertexTarget_cut v) f g hf hg (interiorTime s) (interiorTime t)
    s.property.1 s.property.2 (hs.trans ht.symm)).2.2

include size small_faces in
/-- A point on a vertex ray has exactly that tree vertex as terminal endpoint. -/
theorem small_vertex_rays_iff_endpoint (a : frontier P.body) (T : P.CutLocusTree a)
    (b : frontier P.body) (different : b ≠ a) :
    b ∈ T.vertexRays ↔ b ∉ P.cutSet a ∧
      ((small_cutEndpoint size small_faces a ⟨b, different⟩).val : Space) ∈ T.vertices := by
  constructor
  · intro inside
    obtain ⟨f, inside⟩ := mem_iUnion.mp inside
    obtain ⟨hf, t, at_t⟩ := mem_iUnion.mp inside
    obtain ⟨v, hf⟩ := mem_iUnion.mp hf
    have f0 : f 0 = a := congrArg Prod.fst hf.2
    have f1 : f 1 = T.vertexTarget v := congrArg Prod.snd hf.2
    have outside := small_geodesic_proper_prefix_outside_cutSet size small_faces f hf.1
      (by simpa only [f0, f1] using T.vertexTarget_different v) (interiorTime t) t.property.2
    obtain ⟨nonzero, endpoint⟩ := small_cutEndpoint_on_route size small_faces a _ (T.vertexTarget_cut v)
      f hf (interiorTime t) t.property.1
    have same_input : (⟨f (interiorTime t), nonzero⟩ : {b : frontier P.body // b ≠ a}) =
        ⟨b, different⟩ := Subtype.ext at_t
    rw [same_input] at endpoint
    refine ⟨?_, ?_⟩
    · simpa only [f0, at_t] using outside
    · rw [endpoint]
      exact v.property
  · rintro ⟨outside, endpoint_vertex⟩
    let c := small_cutEndpoint size small_faces a ⟨b, different⟩
    let v : T.vertices := ⟨c.val, endpoint_vertex⟩
    have target : T.vertexTarget v = c.val := rfl
    obtain ⟨f, hf, s, at_s⟩ := P.shortest_extension_path a b c.val
      (small_cutEndpoint_extension size small_faces a ⟨b, different⟩)
    have f0 : f 0 = a := congrArg Prod.fst hf.2
    have f1 : f 1 = c.val := congrArg Prod.snd hf.2
    have positive : 0 < s := lt_of_le_of_ne s.property.1 (by
      intro zero
      have equal : s = 0 := zero.symm
      rw [equal, f0] at at_s
      exact different at_s.symm)
    have before : s < 1 := lt_of_le_of_ne s.property.2 (by
      intro one
      have equal : s = 1 := one
      rw [equal, f1] at at_s
      exact outside (at_s ▸ c.property))
    apply mem_iUnion.mpr
    refine ⟨f, mem_iUnion.mpr ⟨mem_iUnion.mpr ⟨v, ?_⟩, ?_⟩⟩
    · simpa only [target] using hf
    · exact ⟨⟨s, positive, before⟩, at_s⟩

end SixVertexUnfolding.ConvexPolyhedron
