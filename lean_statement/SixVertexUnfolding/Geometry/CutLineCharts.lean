import SixVertexUnfolding.Geometry.EdgeCutLocusStructure
import SixVertexUnfolding.Geometry.FaceCutLocusStructure
import SixVertexUnfolding.Geometry.SurfaceFlatCharts

/-! A two-route point has an actual flat surface neighborhood in which
the multiple-route locus is exactly one straight line. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A flat surface chart carrying the multiple-route locus to one explicit line. -/
structure CutLineChart (P : ConvexPolyhedron) (a : Space) (b : Space) extends P.FlatChart b where
  normal : Plane
  normal_ne_zero : normal ≠ 0
  level : ℝ
  cut_line : ∀ x ∈ domain, map x ∈ P.multipleRouteLocus a ↔ inner ℝ normal x = level

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem cut_line_chart_in_face (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (bF : (b : Space) ∈ F.val)
    (unique : ∀ G : P.Face, (b : Space) ∈ G.val → G = F)
    (two : Nat.card (P.geodesicFiber a b) = 2) : Nonempty (P.CutLineChart a b) := by
  obtain ⟨p, _, q, _, distinct, V, openV, bV, diagram⟩ :=
    graph.two_route_local_bisector small_faces a b different F unique two
  obtain ⟨center, inside⟩ := P.solid
  obtain ⟨facets⟩ := P.exists_normalized_facets inside
  obtain ⟨O, openO, bO, plane⟩ := facets.single_face_local_plane F bF unique
  obtain ⟨lift, in_plane, coordinate, inverse, rigid⟩ :=
    F.exists_rigid_plane_inverse (P.faceCoordinates F) (P.faceCoordinates_rigid F)
  let D : Set Plane := lift ⁻¹' (V ∩ O)
  have origin : P.faceCoordinates F b ∈ D := by
    change lift (P.faceCoordinates F b) ∈ V ∩ O
    rw [inverse b (subset_affineSpan ℝ _ bF)]
    exact ⟨bV, bO⟩
  have in_face (x : Plane) (hx : x ∈ D) : lift x ∈ F.val := by
    have member : lift x ∈ O ∩ (affineSpan ℝ F.val : Set Space) := ⟨hx.2, in_plane x⟩
    rw [← plane] at member
    exact member.2
  obtain ⟨U, openU, bU, covered⟩ := P.unique_face_neighborhood F unique
  refine ⟨{
    domain := D
    open_domain := (openV.inter openO).preimage lift.continuous_of_finiteDimensional
    origin := P.faceCoordinates F b
    origin_mem := origin
    map := lift
    continuous := lift.continuous_of_finiteDimensional
    at_origin := inverse b (subset_affineSpan ℝ _ bF)
    on_surface := fun x hx => F.subset_frontier (in_face x hx)
    distance := fun x hx y hy => (P.surfaceDist_eq_dist_in_face F (in_face x hx) (in_face y hy)).trans (rigid x y)
    covers := ⟨U ∩ (V ∩ O), openU.inter (openV.inter openO), ⟨bU, bV, bO⟩, ?_⟩
    normal := q - p
    normal_ne_zero := sub_ne_zero.mpr distinct.symm
    level := (‖q‖ ^ 2 - ‖p‖ ^ 2) / 2
    cut_line := ?_ }⟩
  · intro x hx
    have xF := (covered x ⟨hx.1.1, hx.2⟩).1
    refine ⟨P.faceCoordinates F x, ?_, inverse x (subset_affineSpan ℝ _ xF)⟩
    change lift (P.faceCoordinates F x) ∈ V ∩ O
    rw [inverse x (subset_affineSpan ℝ _ xF)]
    exact hx.1.2
  · intro x hx
    rw [diagram (lift x) ⟨hx.1, in_face x hx⟩, coordinate x]
    exact equal_site_distances_iff_bisector p q x

include graph small_faces in
theorem cut_line_chart_at_edge (a b : frontier P.body) (different : a ≠ b)
    (F G : P.Face) (shared : P.ShareEdge F G) (target : (b : Space) ∈ F.val ∩ G.val)
    (not_vertex : (b : Space) ∉ P.vertices) (two : Nat.card (P.geodesicFiber a b) = 2) :
    Nonempty (P.CutLineChart a b) := by
  obtain ⟨center, inside⟩ := P.solid
  obtain ⟨facets⟩ := P.exists_normalized_facets inside
  obtain ⟨chart⟩ := exists_edge_folding facets F G shared
  obtain ⟨patch⟩ := chart.exists_metric_patch shared target not_vertex
  obtain ⟨p, _, q, _, distinct, V, openV, bV, contained, diagram⟩ :=
    patch.two_route_local_bisector graph small_faces a b different patch.center_mem two
  let D := patch.sheet.domain ∩ chart.fold.map ⁻¹' V
  have origin : chart.unfold b ∈ D := by
    refine ⟨patch.unfold_mem ⟨patch.center_mem, b.property⟩, ?_⟩
    change chart.fold.map (chart.unfold b) ∈ V
    rwa [chart.fold_unfold (Or.inl target.1)]
  have on_surface (x : Plane) (hx : x ∈ D) : chart.fold.map x ∈ frontier P.body :=
    patch.sheet.on_surface ⟨x, hx.1, rfl⟩
  refine ⟨{
    domain := D
    open_domain := patch.sheet.open_domain.inter (openV.preimage chart.fold.continuous)
    origin := chart.unfold b
    origin_mem := origin
    map := chart.fold.map
    continuous := chart.fold.continuous
    at_origin := chart.fold_unfold (Or.inl target.1)
    on_surface := on_surface
    distance := ?_
    covers := ⟨V, openV, bV, ?_⟩
    normal := q - p
    normal_ne_zero := sub_ne_zero.mpr distinct.symm
    level := (‖q‖ ^ 2 - ‖p‖ ^ 2) / 2
    cut_line := ?_ }⟩
  · intro x hx y hy
    rw [patch.metric _ ⟨contained hx.2, on_surface x hx⟩ _ ⟨contained hy.2, on_surface y hy⟩,
      EdgeFolding.Neighborhood.unfold_fold chart patch.sheet hx.1,
      EdgeFolding.Neighborhood.unfold_fold chart patch.sheet hy.1]
  · intro x hx
    have xpatch : x ∈ patch.domain ∩ frontier P.body := ⟨contained hx.1, hx.2⟩
    refine ⟨chart.unfold x, ⟨patch.unfold_mem xpatch, ?_⟩, chart.fold_unfold (patch.on_facets xpatch)⟩
    change chart.fold.map (chart.unfold x) ∈ V
    rw [chart.fold_unfold (patch.on_facets xpatch)]
    exact hx.1
  · intro x hx
    rw [diagram _ ⟨hx.2, on_surface x hx⟩, EdgeFolding.Neighborhood.unfold_fold chart patch.sheet hx.1]
    exact equal_site_distances_iff_bisector p q x

include graph small_faces in
/-- Every nonvertex point with exactly two routes has a flat chart of the actual cut line. -/
theorem cut_line_chart (a b : frontier P.body) (different : a ≠ b)
    (not_vertex : (b : Space) ∉ P.vertices) (two : Nat.card (P.geodesicFiber a b) = 2) :
    Nonempty (P.CutLineChart a b) := by
  rcases P.nonvertex_incident_facets b.property not_vertex with
    ⟨F, target, unique⟩ | ⟨F, G, shared, target, _⟩
  · exact graph.cut_line_chart_in_face small_faces a b different F target unique two
  · exact graph.cut_line_chart_at_edge small_faces a b different F G shared target not_vertex two

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
