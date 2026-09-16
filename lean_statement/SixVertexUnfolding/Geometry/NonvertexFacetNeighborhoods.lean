import SixVertexUnfolding.Geometry.DualConnectivity
import SixVertexUnfolding.Geometry.EdgeIncidence

/-! Away from the original vertices, a boundary point belongs to at most two
facets. A sufficiently small neighborhood meets only those incident facets. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter
open scoped Topology

/-- Any facet through the interior of an original edge contains that whole edge. -/
theorem Face.contains_edge_of_interior_point {P : ConvexPolyhedron} (F G H : P.Face)
    (shared : P.ShareEdge F G) {z : Space} (hz : z ∈ F.val ∩ G.val)
    (not_vertex : z ∉ P.vertices) (zH : z ∈ H.val) : H = F ∨ H = G := by
  obtain ⟨p, p_vertex, q, q_vertex, _, edge⟩ := F.shared_edge_endpoints G shared
  have inside : z ∈ openSegment ℝ p q := mem_openSegment_of_ne_left_right
    (fun equal => not_vertex (equal ▸ p_vertex))
    (fun equal => not_vertex (equal ▸ q_vertex)) (edge ▸ hz)
  have pH := H.isExposed.isExtreme.left_mem_of_mem_openSegment
    (P.vertices_subset_body p_vertex) (P.vertices_subset_body q_vertex) zH inside
  have qH := H.isExposed.isExtreme.right_mem_of_mem_openSegment
    (P.vertices_subset_body p_vertex) (P.vertices_subset_body q_vertex) zH inside
  apply F.facets_containing_shared_edge G shared H
  rw [edge]
  exact H.convex.segment_subset pH qH

/-- A nonvertex boundary point has either one incident face or exactly two. -/
theorem nonvertex_incident_facets (P : ConvexPolyhedron) {z : Space}
    (surface : z ∈ frontier P.body) (not_vertex : z ∉ P.vertices) :
    (∃ F : P.Face, z ∈ F.val ∧ ∀ H : P.Face, z ∈ H.val → H = F) ∨
    (∃ F G : P.Face, P.ShareEdge F G ∧ z ∈ F.val ∩ G.val ∧
      ∀ H : P.Face, z ∈ H.val → H = F ∨ H = G) := by
  obtain ⟨F, zF⟩ := P.boundary_point_in_face surface
  by_cases only : ∀ H : P.Face, z ∈ H.val → H = F
  · exact Or.inl ⟨F, zF, only⟩
  push Not at only
  obtain ⟨G, zG, different⟩ := only
  have edge := F.shareEdge_of_common_nonvertex G different.symm ⟨zF, zG⟩ not_vertex
  exact Or.inr ⟨F, G, edge, ⟨zF, zG⟩,
    fun H zH => F.contains_edge_of_interior_point G H edge ⟨zF, zG⟩ not_vertex zH⟩

/-- Near any boundary point, no new facet appears that does not contain the point itself. -/
theorem incident_facets_neighborhood (P : ConvexPolyhedron) (z : Space) :
    ∃ U : Set Space, IsOpen U ∧ z ∈ U ∧
      ∀ w ∈ U, ∀ F : P.Face, w ∈ F.val → z ∈ F.val := by
  let absent := {F : P.Face // z ∉ F.val}
  let forbidden : Set Space := ⋃ F : absent, F.val.val
  have closed : IsClosed forbidden := isClosed_iUnion_of_finite (fun F => F.val.isClosed)
  refine ⟨forbiddenᶜ, closed.isOpen_compl, ?_, ?_⟩
  · intro member
    obtain ⟨F, zF⟩ := mem_iUnion.mp member
    exact F.property zF
  · intro w near F wF
    by_contra zF
    exact near (mem_iUnion.mpr ⟨⟨F, zF⟩, wF⟩)

/-- Around the interior of an edge, the surface is contained in precisely its two incident facets. -/
theorem edge_neighborhood_two_facets (P : ConvexPolyhedron) (F G : P.Face)
    (shared : P.ShareEdge F G) {z : Space} (hz : z ∈ F.val ∩ G.val)
    (not_vertex : z ∉ P.vertices) :
    ∃ U : Set Space, IsOpen U ∧ z ∈ U ∧
      U ∩ frontier P.body ⊆ F.val ∪ G.val := by
  obtain ⟨U, openU, zU, incident⟩ := P.incident_facets_neighborhood z
  refine ⟨U, openU, zU, ?_⟩
  intro w hw
  obtain ⟨H, wH⟩ := P.boundary_point_in_face hw.2
  rcases F.contains_edge_of_interior_point G H shared hz not_vertex (incident w hw.1 H wH) with rfl | rfl
  exacts [Or.inl wH, Or.inr wH]

end SixVertexUnfolding.ConvexPolyhedron
