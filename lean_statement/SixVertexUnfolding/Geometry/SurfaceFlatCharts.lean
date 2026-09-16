import SixVertexUnfolding.Geometry.EdgeLocalMetric

/-! Away from the original vertices, the actual polyhedral boundary admits
planar neighborhoods preserving its shortest-path metric. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- An internal flat neighborhood with its actual surface map and metric meaning. -/
structure FlatChart (P : ConvexPolyhedron) (z : Space) where
  domain : Set Plane
  open_domain : IsOpen domain
  origin : Plane
  origin_mem : origin ∈ domain
  map : Plane → Space
  continuous : Continuous map
  at_origin : map origin = z
  on_surface : MapsTo map domain (frontier P.body)
  distance : ∀ x ∈ domain, ∀ y ∈ domain, P.surfaceDist (map x) (map y) = dist x y
  covers : ∃ U : Set Space, IsOpen U ∧ z ∈ U ∧ U ∩ frontier P.body ⊆ map '' domain

namespace EdgeFolding

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G)

/-- Any positive planar disk covers some neighborhood of its central edge point. -/
theorem disk_covers_neighborhood (shared : P.ShareEdge F G) {z : Space}
    (hz : z ∈ F.val ∩ G.val) (not_vertex : z ∉ P.vertices) {ε : ℝ} (positive : 0 < ε) :
    ∃ U : Set Space, IsOpen U ∧ z ∈ U ∧
      U ∩ frontier P.body ⊆ chart.fold.map '' Metric.ball (chart.left z) ε := by
  obtain ⟨U₀, open₀, z₀, only_two⟩ := P.edge_neighborhood_two_facets F G shared hz not_vertex
  let V := Metric.ball (chart.left z) ε
  let U : Set Space := U₀ ∩ (chart.left ⁻¹' V ∩ chart.right ⁻¹' V)
  have openU : IsOpen U := open₀.inter
    ((Metric.isOpen_ball.preimage chart.left.continuous_of_finiteDimensional).inter
      (Metric.isOpen_ball.preimage chart.right.continuous_of_finiteDimensional))
  have origin : chart.left z ∈ V := Metric.mem_ball_self positive
  have zU : z ∈ U := ⟨z₀, origin, by change chart.right z ∈ V; rwa [← chart.joined hz]⟩
  refine ⟨U, openU, zU, ?_⟩
  intro x hx
  rcases only_two ⟨hx.1.1, hx.2⟩ with first | second
  · exact ⟨chart.left x, hx.1.2.1, chart.fold_left first⟩
  · exact ⟨chart.right x, hx.1.2.2, chart.fold_right second⟩

include chart in
/-- The constructed edge neighborhood supplies a flat chart in the intrinsic metric. -/
theorem flat_chart (shared : P.ShareEdge F G) {z : Space}
    (hz : z ∈ F.val ∩ G.val) (not_vertex : z ∉ P.vertices) : Nonempty (P.FlatChart z) := by
  obtain ⟨near⟩ := chart.exists_neighborhood shared hz not_vertex
  obtain ⟨ε, positive, disk_in, isometric⟩ := near.exists_isometric_disk shared hz not_vertex
  exact ⟨{
    domain := Metric.ball (chart.left z) ε
    open_domain := Metric.isOpen_ball
    origin := chart.left z
    origin_mem := Metric.mem_ball_self positive
    map := chart.fold.map
    continuous := chart.fold.continuous
    at_origin := chart.fold_left hz.1
    on_surface := fun x hx => near.on_surface ⟨x, disk_in hx, rfl⟩
    distance := isometric
    covers := chart.disk_covers_neighborhood shared hz not_vertex positive }⟩

end EdgeFolding

/-- A point belonging to only one original face has a rigid planar chart. -/
theorem flat_chart_in_single_face {P : ConvexPolyhedron} (F : P.Face) {z : Space}
    (hz : z ∈ F.val) (unique : ∀ G : P.Face, z ∈ G.val → G = F) : Nonempty (P.FlatChart z) := by
  obtain ⟨center, inside⟩ := P.solid
  obtain ⟨facets⟩ := P.exists_normalized_facets inside
  obtain ⟨U₁, open₁, z₁, plane⟩ := facets.single_face_local_plane F hz unique
  obtain ⟨place, rigid⟩ := F.exists_rigid_placement
  obtain ⟨lift, in_plane, left_inverse, right_inverse, lift_rigid⟩ := F.exists_rigid_plane_inverse place rigid
  let V : Set Plane := lift ⁻¹' U₁
  have openV : IsOpen V := open₁.preimage lift.continuous_of_finiteDimensional
  have origin : place z ∈ V := by change lift (place z) ∈ U₁; rwa [right_inverse z (subset_affineSpan ℝ _ hz)]
  have in_face (x : Plane) (hx : x ∈ V) : lift x ∈ F.val := by
    have member : lift x ∈ U₁ ∩ (affineSpan ℝ F.val : Set Space) := ⟨hx, in_plane x⟩
    rw [← plane] at member
    exact member.2
  obtain ⟨U₀, open₀, z₀, incident⟩ := P.incident_facets_neighborhood z
  let U : Set Space := U₀ ∩ place ⁻¹' V
  have openU : IsOpen U := open₀.inter (openV.preimage place.continuous_of_finiteDimensional)
  have covered : U ∩ frontier P.body ⊆ lift '' V := by
    intro x hx
    obtain ⟨G, xG⟩ := P.boundary_point_in_face hx.2
    have same := unique G (incident x hx.1.1 G xG)
    subst G
    exact ⟨place x, hx.1.2, right_inverse x (subset_affineSpan ℝ _ xG)⟩
  exact ⟨{
    domain := V, open_domain := openV, origin := place z, origin_mem := origin
    map := lift, continuous := lift.continuous_of_finiteDimensional
    at_origin := right_inverse z (subset_affineSpan ℝ _ hz)
    on_surface := fun x hx => F.subset_frontier (in_face x hx)
    distance := fun x hx y hy => (P.surfaceDist_eq_dist_in_face F (in_face x hx) (in_face y hy)).trans (lift_rigid x y)
    covers := ⟨U, openU, ⟨z₀, origin⟩, covered⟩ }⟩

/-- Every boundary point except an original vertex has an actual flat metric chart. -/
theorem exists_flat_chart (P : ConvexPolyhedron) {z : Space}
    (surface : z ∈ frontier P.body) (not_vertex : z ∉ P.vertices) : Nonempty (P.FlatChart z) := by
  rcases P.nonvertex_incident_facets surface not_vertex with ⟨F, hz, unique⟩ | ⟨F, G, shared, hz, _⟩
  · exact flat_chart_in_single_face F hz unique
  · obtain ⟨center, inside⟩ := P.solid
    obtain ⟨facets⟩ := P.exists_normalized_facets inside
    obtain ⟨chart⟩ := exists_edge_folding facets F G shared
    exact chart.flat_chart shared hz not_vertex

end SixVertexUnfolding.ConvexPolyhedron
