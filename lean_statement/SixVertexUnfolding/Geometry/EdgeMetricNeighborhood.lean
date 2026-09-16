import SixVertexUnfolding.Geometry.SurfaceFlatCharts

/-! Near an original edge point, the joined face coordinates preserve the
actual intrinsic distance and every incident face is one of the two originals. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G)

/-- An ambient neighborhood where both face incidence and intrinsic distances use one joined development. -/
theorem exists_metric_neighborhood (shared : P.ShareEdge F G) {z : Space}
    (hz : z ∈ F.val ∩ G.val) (not_vertex : z ∉ P.vertices) :
    ∃ U : Set Space, IsOpen U ∧ z ∈ U ∧
      (∀ x ∈ U, ∀ H : P.Face, x ∈ H.val → H = F ∨ H = G) ∧
      U ∩ frontier P.body ⊆ F.val ∪ G.val ∧
      ∀ x ∈ U ∩ frontier P.body, ∀ y ∈ U ∩ frontier P.body,
        P.surfaceDist x y = dist (chart.unfold x) (chart.unfold y) := by
  obtain ⟨near⟩ := chart.exists_neighborhood shared hz not_vertex
  obtain ⟨ε, positive, disk_in, metric⟩ := near.exists_isometric_disk shared hz not_vertex
  obtain ⟨V, openV, zV, covers⟩ := chart.disk_covers_neighborhood shared hz not_vertex positive
  obtain ⟨W, openW, zW, incident⟩ := P.incident_facets_neighborhood z
  have only_two (x : Space) (xW : x ∈ W) (H : P.Face) (xH : x ∈ H.val) : H = F ∨ H = G :=
    F.contains_edge_of_interior_point G H shared hz not_vertex (incident x xW H xH)
  refine ⟨V ∩ W, openV.inter openW, ⟨zV, zW⟩, fun x hx H xH => only_two x hx.2 H xH, ?_, ?_⟩
  · intro x hx
    obtain ⟨H, xH⟩ := P.boundary_point_in_face hx.2
    rcases only_two x hx.1.2 H xH with rfl | rfl
    exacts [Or.inl xH, Or.inr xH]
  · intro x hx y hy
    obtain ⟨p, hp, rfl⟩ := covers ⟨hx.1.1, hx.2⟩
    obtain ⟨q, hq, rfl⟩ := covers ⟨hy.1.1, hy.2⟩
    rw [Neighborhood.unfold_fold chart near (disk_in hp), Neighborhood.unfold_fold chart near (disk_in hq)]
    exact metric p hp q hq

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
