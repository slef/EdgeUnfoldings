import SixVertexUnfolding.Geometry.CutTreeTriangleCoverage
import SixVertexUnfolding.Geometry.CutEdgeRegionIndependence

/-! Around a tree vertex, only its incident paired radial triangles are
needed to cover the surface. This includes original cone vertices. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- A tree vertex contained in a closed strip must be one of its base endpoints. -/
theorem tree_vertex_in_closed_strip (a : frontier P.body) (T : P.CutLocusTree a)
    {v w : T.vertices} (edge : T.graph.Adj v w)
    (routes : C(unitInterval, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t))
    (u : T.vertices) (inside : T.vertexTarget u ∈ range (closedRouteStripMap routes)) :
    u = v ∨ u = w := by
  obtain ⟨⟨s, t⟩, at_u⟩ := inside
  change routes s t = T.vertexTarget u at at_u
  have first : routes s 0 = a := congrArg Prod.fst (member s).2
  have last : routes s 1 = T.closedEdgeTarget edge s := congrArg Prod.snd (member s).2
  have different : routes s 0 ≠ routes s 1 := by
    rw [first, last]
    intro equal
    have cut := T.closedEdgeTarget_cut edge s
    rw [← equal] at cut
    exact P.source_not_cutSet a cut
  have at_end : t = 1 := by
    by_contra before
    have outside := graph.geodesic_proper_prefix_outside_cutSet small_faces (routes s) (member s).1
      different t (lt_of_le_of_ne t.property.2 before)
    rw [first, at_u] at outside
    exact outside (T.vertexTarget_cut u)
  rw [at_end, last] at at_u
  by_cases at_left : s = 0
  · rw [at_left, T.closedEdgeTarget_zero] at at_u
    exact Or.inl (Subtype.ext (congrArg Subtype.val at_u).symm)
  by_cases at_right : s = 1
  · rw [at_right, T.closedEdgeTarget_one] at at_u
    exact Or.inr (Subtype.ext (congrArg Subtype.val at_u).symm)
  have interior : (T.closedEdgeTarget edge s : Space) ∈ openSegment ℝ (v : Space) (w : Space) :=
    lineMap_mem_openSegment ℝ _ _ ⟨lt_of_le_of_ne s.property.1
      (fun equal => at_left (Subtype.ext equal.symm)),
      lt_of_le_of_ne s.property.2 (fun equal => at_right (Subtype.ext equal))⟩
  rw [at_u] at interior
  exact (disjoint_left.mp (T.no_vertex_inside v w edge) interior u.property).elim

include graph small_faces in
/-- All sufficiently nearby surface points lie in outgoing incident triangles. -/
theorem incident_triangles_cover_neighborhood (a : frontier P.body) (T : P.CutLocusTree a)
    (triangles : (d : T.graph.Dart) → CutEdgeTriangles T d.adj) (u : T.vertices) :
    ∃ U : Set (frontier P.body), IsOpen U ∧ T.vertexTarget u ∈ U ∧
      ∀ b ∈ U, ∃ v : T.vertices, ∃ edge : T.graph.Adj u v,
        b ∈ (triangles ⟨(u, v), edge⟩).region := by
  classical
  letI : Fintype T.vertices := T.finite_vertices.fintype
  let others := {d : T.graph.Dart // d.fst ≠ u ∧ d.snd ≠ u}
  let bad : Set (frontier P.body) := ⋃ d : others, (triangles d.val).region
  have closed : IsClosed bad := isClosed_iUnion_of_finite (fun d => (triangles d.val).region_closed)
  have avoids : T.vertexTarget u ∉ bad := by
    intro inside
    obtain ⟨d, inside⟩ := mem_iUnion.mp inside
    have endpoints : u = d.val.fst ∨ u = d.val.snd := by
      rcases inside with first | second
      · exact graph.tree_vertex_in_closed_strip small_faces a T d.val.adj (triangles d.val).first
          (fun t => ((triangles d.val).member t).1) u first
      · exact graph.tree_vertex_in_closed_strip small_faces a T d.val.adj (triangles d.val).second
          (fun t => ((triangles d.val).member t).2) u second
    exact endpoints.elim (fun equal => d.property.1 equal.symm) (fun equal => d.property.2 equal.symm)
  refine ⟨badᶜ, closed.isOpen_compl, avoids, ?_⟩
  intro b near
  obtain ⟨⟨⟨v, w⟩, edge⟩, inside⟩ := graph.cut_tree_triangles_cover small_faces a T triangles b
  by_cases left : v = u
  · subst v
    exact ⟨w, edge, inside⟩
  by_cases right : w = u
  · subst w
    refine ⟨v, edge.symm, ?_⟩
    change b ∈ (triangles ⟨(v, u), edge⟩).region at inside
    rwa [graph.reverse_cut_edge_regions small_faces a T
      (triangles ⟨(v, u), edge⟩) (triangles ⟨(u, v), edge.symm⟩)] at inside
  · exact (near (mem_iUnion.mpr ⟨⟨⟨(v, w), edge⟩, left, right⟩, inside⟩)).elim

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
