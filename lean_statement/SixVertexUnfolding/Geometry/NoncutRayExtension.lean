import SixVertexUnfolding.Geometry.PlanarRayExtension
import SixVertexUnfolding.Geometry.EdgeRouteSourceNeighborhoods
import SixVertexUnfolding.Geometry.UniqueRouteSourceDistance
import SixVertexUnfolding.Geometry.CutSetContraction

/-! A shortest route can continue strictly past any target outside the cut
set other than its source. Face interiors and original edges are both covered. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem shortest_extension_in_face (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (bF : (b : Space) ∈ F.val)
    (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F)
    (unique_route : (P.geodesicFiber a b).Subsingleton) :
    ∃ c ∈ P.shortestExtensions a b, c ≠ b := by
  obtain ⟨source, _, U, openU, bU, formula⟩ :=
    graph.unique_route_source_distance small_faces a b different F unique_face unique_route
  obtain ⟨center, inside⟩ := P.solid
  obtain ⟨facets⟩ := P.exists_normalized_facets inside
  obtain ⟨O, openO, bO, plane⟩ := facets.single_face_local_plane F bF unique_face
  obtain ⟨lift, in_plane, coordinate, inverse, _⟩ :=
    F.exists_rigid_plane_inverse (P.faceCoordinates F) (P.faceCoordinates_rigid F)
  let V : Set Plane := lift ⁻¹' (U ∩ O)
  have origin : lift (P.faceCoordinates F b) = b := inverse b (subset_affineSpan ℝ _ bF)
  have in_face (x : Plane) (hx : x ∈ V) : lift x ∈ F.val := by
    have member : lift x ∈ O ∩ (affineSpan ℝ F.val : Set Space) := ⟨hx.2, in_plane x⟩
    rw [← plane] at member
    exact member.2
  apply P.shortest_extension_of_planar_formula a b different source (P.faceCoordinates F b) lift V
    ((openU.inter openO).preimage lift.continuous_of_finiteDimensional)
    (by change lift (P.faceCoordinates F b) ∈ U ∩ O; rw [origin]; exact ⟨bU, bO⟩) origin
    (fun x hx => F.subset_frontier (in_face x hx))
  · intro x hx
    rw [P.surfaceDist_eq_dist_in_face F bF (in_face x hx),
      ← P.faceCoordinates_rigid F b bF (lift x) (in_face x hx), coordinate]
  · intro x hx
    rw [formula (lift x) ⟨hx.1, F.subset_frontier (in_face x hx)⟩, coordinate]

include graph small_faces in
theorem shortest_extension_at_edge (a b : frontier P.body) (different : a ≠ b)
    (not_vertex : (b : Space) ∉ P.vertices)
    (F G : P.Face) (shared : P.ShareEdge F G) (target : (b : Space) ∈ F.val ∩ G.val)
    (unique_route : (P.geodesicFiber a b).Subsingleton) :
    ∃ c ∈ P.shortestExtensions a b, c ≠ b := by
  obtain ⟨center, inside⟩ := P.solid
  obtain ⟨facets⟩ := P.exists_normalized_facets inside
  obtain ⟨chart⟩ := exists_edge_folding facets F G shared
  obtain ⟨patch⟩ := chart.exists_metric_patch shared target not_vertex
  obtain ⟨source, _, U, openU, bU, formula⟩ :=
    patch.unique_route_source_distance graph small_faces a b different patch.center_mem unique_route
  let V : Set Plane := patch.sheet.domain ∩ chart.fold.map ⁻¹' (U ∩ patch.domain)
  have origin : chart.fold.map (chart.unfold b) = b := chart.fold_unfold (Or.inl target.1)
  have on_surface (x : Plane) (hx : x ∈ V) : chart.fold.map x ∈ frontier P.body :=
    patch.sheet.on_surface ⟨x, hx.1, rfl⟩
  apply P.shortest_extension_of_planar_formula a b different source (chart.unfold b) chart.fold.map V
    (patch.sheet.open_domain.inter ((openU.inter patch.open_domain).preimage chart.fold.continuous))
    ⟨patch.unfold_mem ⟨patch.center_mem, b.property⟩,
      by change chart.fold.map (chart.unfold b) ∈ U ∩ patch.domain; rw [origin]; exact ⟨bU, patch.center_mem⟩⟩
    origin on_surface
  · intro x hx
    rw [patch.metric b ⟨patch.center_mem, b.property⟩ _ ⟨hx.2.2, on_surface x hx⟩,
      EdgeFolding.Neighborhood.unfold_fold chart patch.sheet hx.1]
  · intro x hx
    rw [formula _ ⟨hx.2.1, on_surface x hx⟩,
      EdgeFolding.Neighborhood.unfold_fold chart patch.sheet hx.1]

include graph small_faces in
/-- A noncut point other than the source is never a final shortest-ray endpoint. -/
theorem shortest_extension_outside_cutSet (a b : frontier P.body) (different : a ≠ b)
    (outside : b ∉ P.cutSet a) : ∃ c ∈ P.shortestExtensions a b, c ≠ b := by
  have not_vertex : (b : Space) ∉ P.vertices := fun vertex => outside (Or.inr ⟨vertex, different.symm⟩)
  have unique_route := P.unique_outside_cutSet a b outside
  rcases P.nonvertex_incident_facets b.property not_vertex with
    ⟨F, bF, unique_face⟩ | ⟨F, G, shared, target, _⟩
  · exact graph.shortest_extension_in_face small_faces a b different F bF unique_face unique_route
  · exact graph.shortest_extension_at_edge small_faces a b different not_vertex F G shared target unique_route

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
