import SixVertexUnfolding.Geometry.EdgeCutLocusStructure
import SixVertexUnfolding.Geometry.FaceCutLocusStructure
import SixVertexUnfolding.Geometry.SurfaceFlatCharts

/-! Every nonvertex target has a flat chart in which the actual cut locus
is the Voronoi boundary of finitely many active shortest-route sources. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A flat chart with the exact finite nearest-source description of the cut locus. -/
structure CutVoronoiChart (P : ConvexPolyhedron) (a b : frontier P.body) extends P.FlatChart b where
  sources : Set Plane
  finite_sources : sources.Finite
  source_distance : ∀ p ∈ sources, dist p origin = P.surfaceDist a b
  route_count : sources.ncard = Nat.card (P.geodesicFiber a b)
  local_distance : ∀ x ∈ domain,
    (∀ p ∈ sources, P.surfaceDist a (map x) ≤ dist p x) ∧
      ∃ p ∈ sources, P.surfaceDist a (map x) = dist p x
  cut_diagram : ∀ x ∈ domain, map x ∈ P.multipleRouteLocus a ↔ x ∈ voronoiBoundary sources
  source_routes : ∀ p, p ∈ sources ↔ ∃ f ∈ P.geodesicFiber a b,
    ∃ start : unitInterval, start < 1 ∧ ∀ t ∈ Icc start 1,
      AffineMap.lineMap p origin (t : ℝ) ∈ domain ∧
      map (AffineMap.lineMap p origin (t : ℝ)) = (f t : Space)
  route_stability : ∀ (p : Plane) (f : P.BoundaryCurve), f ∈ P.geodesicFiber a b →
    (∃ start : unitInterval, start < 1 ∧ ∀ t ∈ Icc start 1,
      AffineMap.lineMap p origin (t : ℝ) ∈ domain ∧
      map (AffineMap.lineMap p origin (t : ℝ)) = (f t : Space)) →
    ∃ W : Set P.BoundaryCurve, IsOpen W ∧ f ∈ W ∧
      ∀ g ∈ W, g ∈ P.geodesicCurves → g 0 = a →
        ∀ x ∈ domain, map x = (g 1 : Space) → P.surfaceDist a (map x) = dist p x

/-- A straight segment eventually stays in any open neighborhood of its endpoint. -/
private theorem lineMap_tail_in_open (p z : Plane) {D : Set Plane}
    (openD : IsOpen D) (zD : z ∈ D) :
    ∃ start : unitInterval, start < 1 ∧ ∀ t ∈ Icc start 1,
      AffineMap.lineMap p z (t : ℝ) ∈ D := by
  have continuous : Continuous (fun t : ℝ => AffineMap.lineMap p z t) := by
    simp only [AffineMap.lineMap_apply_module]
    exact ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have open_preimage : IsOpen ((fun t : ℝ => AffineMap.lineMap p z t) ⁻¹' D) :=
    openD.preimage continuous
  obtain ⟨ε, positive, interval⟩ := Metric.isOpen_iff.mp open_preimage 1 (by simpa using zD)
  obtain ⟨s, after, before⟩ := exists_between
    (show max (0 : ℝ) (1 - ε) < 1 from max_lt (by norm_num) (by linarith))
  refine ⟨⟨s, (le_max_left _ _).trans after.le, before.le⟩, before, ?_⟩
  intro t ht
  apply interval
  change dist (t : ℝ) 1 < ε
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr t.property.2)]
  have lower : s ≤ (t : ℝ) := ht.1
  have := (le_max_right (0 : ℝ) (1 - ε)).trans_lt after
  linarith

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem cut_voronoi_chart_in_face (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (bF : (b : Space) ∈ F.val)
    (unique : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) : Nonempty (P.CutVoronoiChart a b) := by
  obtain ⟨V₀, openV₀, bV₀, diagram₀⟩ :=
    graph.local_voronoi_cut_locus small_faces a b different F unique
  obtain ⟨W, openW, bW, minimum₀⟩ :=
    graph.local_minimum_distance small_faces a b different F unique
  let V := V₀ ∩ W
  have openV : IsOpen V := openV₀.inter openW
  have bV : (b : Space) ∈ V := ⟨bV₀, bW⟩
  have diagram (x : Space) (hx : x ∈ V ∩ F.val) := diagram₀ x ⟨hx.1.1, hx.2⟩
  have minimum (x : Space) (hx : x ∈ V ∩ F.val) := minimum₀ x ⟨hx.1.2, hx.2⟩
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
    sources := P.activeSources a b F
    finite_sources := graph.activeSources_finite small_faces a b different F unique
    source_distance := fun p hp => (P.activeSource_distance a b F p hp).symm
    route_count := graph.activeSources_ncard small_faces a b different F unique
    local_distance := ?_
    cut_diagram := ?_
    source_routes := ?_
    route_stability := ?_ }⟩
  · intro x hx
    have xF := (covered x ⟨hx.1.1, hx.2⟩).1
    refine ⟨P.faceCoordinates F x, ?_, inverse x (subset_affineSpan ℝ _ xF)⟩
    change lift (P.faceCoordinates F x) ∈ V ∩ O
    rw [inverse x (subset_affineSpan ℝ _ xF)]
    exact hx.1.2
  · intro x hx
    simpa only [coordinate x] using minimum (lift x) ⟨hx.1, in_face x hx⟩
  · intro x hx
    rw [diagram (lift x) ⟨hx.1, in_face x hx⟩, coordinate x]
  · intro p
    constructor
    · rintro ⟨f, hf, s, before, tail⟩
      have last : f 1 = b := congrArg Prod.snd hf.2
      obtain ⟨u, ub, near⟩ := lineMap_tail_in_open p (P.faceCoordinates F b)
        ((openV.inter openO).preimage lift.continuous_of_finiteDimensional) origin
      refine ⟨f, hf, max s u, max_lt before ub, ?_⟩
      intro t ht
      have position := tail t ⟨(le_max_left s u).trans ht.1, ht.2⟩
      rw [last] at position
      refine ⟨near t ⟨(le_max_right s u).trans ht.1, ht.2⟩, ?_⟩
      rw [← position.2, inverse _ (subset_affineSpan ℝ _ position.1)]
    · rintro ⟨f, hf, s, before, tail⟩
      have last : f 1 = b := congrArg Prod.snd hf.2
      refine ⟨f, hf, s, before, ?_⟩
      intro t ht
      have position := tail t ht
      refine ⟨position.2 ▸ in_face _ position.1, ?_⟩
      rw [last, ← position.2, coordinate]
  · intro p f hf represented
    have first : f 0 = a := congrArg Prod.fst hf.2
    have last : f 1 = b := congrArg Prod.snd hf.2
    have actual : P.HasTerminalSource f F p := by
      obtain ⟨s, before, tail⟩ := represented
      refine ⟨s, before, ?_⟩
      intro t ht
      have position := tail t ht
      refine ⟨position.2 ▸ in_face _ position.1, ?_⟩
      rw [last, ← position.2, coordinate]
    obtain ⟨q, _, terminal, W, openW, fW, formula⟩ :=
      graph.geodesic_branch_distance small_faces f hf.1
        (by simpa only [first, last] using different) F (by simpa only [last] using unique)
    have same : q = p := terminal.unique actual
    refine ⟨W, openW, fW, ?_⟩
    intro g hg geodesic starts x hx mapped
    have value := formula g hg geodesic (starts.trans first.symm)
    rw [starts, same, ← mapped, coordinate] at value
    exact value

include graph small_faces in
theorem cut_voronoi_chart_at_edge (a b : frontier P.body) (different : a ≠ b)
    (F G : P.Face) (shared : P.ShareEdge F G) (target : (b : Space) ∈ F.val ∩ G.val)
    (not_vertex : (b : Space) ∉ P.vertices) :
    Nonempty (P.CutVoronoiChart a b) := by
  obtain ⟨center, inside⟩ := P.solid
  obtain ⟨facets⟩ := P.exists_normalized_facets inside
  obtain ⟨chart⟩ := exists_edge_folding facets F G shared
  obtain ⟨patch⟩ := chart.exists_metric_patch shared target not_vertex
  obtain ⟨V₀, openV₀, bV₀, contained₀, diagram₀⟩ :=
    patch.local_voronoi_cut_locus graph small_faces a b different patch.center_mem
  obtain ⟨W, openW, bW, _, minimum₀⟩ :=
    patch.local_minimum_distance graph small_faces a b different patch.center_mem
  let V := V₀ ∩ W
  have openV : IsOpen V := openV₀.inter openW
  have bV : (b : Space) ∈ V := ⟨bV₀, bW⟩
  have contained : V ⊆ patch.domain := fun _ hx => contained₀ hx.1
  have diagram (x : Space) (hx : x ∈ V ∩ frontier P.body) := diagram₀ x ⟨hx.1.1, hx.2⟩
  have minimum (x : Space) (hx : x ∈ V ∩ frontier P.body) := minimum₀ x ⟨hx.1.2, hx.2⟩
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
    sources := chart.activeSources a b
    finite_sources := patch.activeSources_finite graph small_faces a b different patch.center_mem
    source_distance := fun p hp => (chart.activeSource_distance patch a b patch.center_mem p hp).symm
    route_count := patch.activeSources_ncard graph small_faces a b different patch.center_mem
    local_distance := ?_
    cut_diagram := ?_
    source_routes := ?_
    route_stability := ?_ }⟩
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
    simpa only [EdgeFolding.Neighborhood.unfold_fold chart patch.sheet hx.1] using
      minimum _ ⟨hx.2, on_surface x hx⟩
  · intro x hx
    rw [diagram _ ⟨hx.2, on_surface x hx⟩, EdgeFolding.Neighborhood.unfold_fold chart patch.sheet hx.1]
  · intro p
    constructor
    · rintro ⟨f, hf, s, before, tail⟩
      have last : f 1 = b := congrArg Prod.snd hf.2
      obtain ⟨u, ub, near⟩ := lineMap_tail_in_open p (chart.unfold b)
        (patch.sheet.open_domain.inter (openV.preimage chart.fold.continuous)) origin
      refine ⟨f, hf, max s u, max_lt before ub, ?_⟩
      intro t ht
      have position := tail t ⟨(le_max_left s u).trans ht.1, ht.2⟩
      rw [last] at position
      refine ⟨near t ⟨(le_max_right s u).trans ht.1, ht.2⟩, ?_⟩
      rw [← position.2, chart.fold_unfold position.1]
    · rintro ⟨f, hf, s, before, tail⟩
      have last : f 1 = b := congrArg Prod.snd hf.2
      refine ⟨f, hf, s, before, ?_⟩
      intro t ht
      have position := tail t ht
      refine ⟨position.2 ▸ patch.sheet.on_facets position.1.1, ?_⟩
      rw [last, ← position.2, EdgeFolding.Neighborhood.unfold_fold chart patch.sheet position.1.1]
  · intro p f hf represented
    have first : f 0 = a := congrArg Prod.fst hf.2
    have last : f 1 = b := congrArg Prod.snd hf.2
    have actual : chart.HasTerminalSource f p := by
      obtain ⟨s, before, tail⟩ := represented
      refine ⟨s, before, ?_⟩
      intro t ht
      have position := tail t ht
      refine ⟨position.2 ▸ patch.sheet.on_facets position.1.1, ?_⟩
      rw [last, ← position.2, EdgeFolding.Neighborhood.unfold_fold chart patch.sheet position.1.1]
    obtain ⟨q, _, terminal, W, openW, fW, formula⟩ :=
      patch.geodesic_branch_source graph small_faces f hf.1
        (by simpa only [first, last] using different) (by simpa only [last] using patch.center_mem)
    have same : q = p := chart.terminal_source_unique f q p terminal actual
    refine ⟨W, openW, fW, ?_⟩
    intro g hg geodesic starts x hx mapped
    have value := (formula g hg geodesic (starts.trans first.symm)).2
    rw [starts, same, ← mapped, EdgeFolding.Neighborhood.unfold_fold chart patch.sheet hx.1] at value
    exact value

include graph small_faces in
/-- Every nonsource nonvertex point has a flat chart of its actual finite Voronoi diagram. -/
theorem cut_voronoi_chart (a b : frontier P.body) (different : a ≠ b)
    (not_vertex : (b : Space) ∉ P.vertices) :
    Nonempty (P.CutVoronoiChart a b) := by
  rcases P.nonvertex_incident_facets b.property not_vertex with
    ⟨F, target, unique⟩ | ⟨F, G, shared, target, _⟩
  · exact graph.cut_voronoi_chart_in_face small_faces a b different F target unique
  · exact graph.cut_voronoi_chart_at_edge small_faces a b different F G shared target not_vertex

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
