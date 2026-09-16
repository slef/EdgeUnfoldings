import SixVertexUnfolding.Geometry.SmallPolyhedronShortestRoutes
import SixVertexUnfolding.Geometry.EdgeBranchIsolation
import SixVertexUnfolding.Geometry.NonvertexRouteStability
import SixVertexUnfolding.Geometry.CutSetInSpace

/-! Shortest-route stability and compactness of the actual cut set, for at
most six vertices with triangular or quadrilateral faces. All shortest-path
inputs come from the actual local fans; no canonical graph is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set BoundedContinuousFunction

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Normalized shortest curves that meet internally coincide. -/
theorem small_geodesic_curves_agree_of_meeting (f g : P.BoundaryCurve)
    (hf : f ∈ P.geodesicCurves) (hg : g ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (source : f 0 = g 0) (target : f 1 = g 1)
    (t : unitInterval) (positive : 0 < t) (before : t < 1) (meet : f t = g t) : f = g := by
  obtain ⟨first_shortest, first_finite, first_speed⟩ := P.surfacePathOfCurve_shortest f hf
  obtain ⟨second_shortest, second_finite, second_speed⟩ := P.surfacePathOfCurve_shortest g hg
  have ha : (f 0 : Space) = (g 0 : Space) := congrArg Subtype.val source
  have hb : (f 1 : Space) = (g 1 : Space) := congrArg Subtype.val target
  let second := (P.surfacePathOfCurve g).cast ha hb
  have same := small_shortest_routes_agree_of_meeting size small_faces (P.surfacePathOfCurve f) second
    (fun h => different (Subtype.ext h)) first_shortest
    ((P.surfacePathOfCurve g).cast_shortest ha hb second_shortest) first_finite second_finite
    first_speed second_speed t positive before (congrArg Subtype.val meet)
  apply BoundedContinuousFunction.ext
  intro u
  exact Subtype.ext (same u)

include size small_faces in
/-- The source recovered from a terminal face visit is in the finite source list. -/
theorem small_recoveredSource_mem (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (F : P.Face) (unique : ∀ G : P.Face, (f 1 : Space) ∈ G.val → G = F)
    (t : unitInterval) (before : t < 1) (inside : (f t : Space) ∈ F.val) :
    P.recoveredSource F t f ∈ P.sourceImages (f 0) F := by
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  have avoids := small_shortest_lipschitz_avoids_vertices size small_faces (P.surfacePathOfCurve f)
    (fun h => different (Subtype.ext h)) shortest finite speed
  obtain ⟨source, member, formula⟩ := (P.surfacePathOfCurve f).source_image_at_face_visit
    shortest finite speed avoids F unique t before inside
  exact P.recoveredSource_eq F t before f source formula ▸ member

namespace EdgeFolding

variable {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G)

include size small_faces in
theorem small_exists_terminal_source
    (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves) (different : f 0 ≠ f 1)
    (only_two : ∀ H : P.Face, (f 1 : Space) ∈ H.val → H = F ∨ H = G) :
    ∃ source ∈ chart.sourceImages (f 0), chart.HasTerminalSource f source := by
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  obtain ⟨code, start, before, tail⟩ := (P.surfacePathOfCurve f).exists_terminal_source_code shortest finite speed
    (small_shortest_lipschitz_avoids_vertices size small_faces _ (fun h => different (Subtype.ext h)) shortest finite speed)
  have target := (tail 1 ⟨unitInterval.le_one', le_rfl⟩).1
  have terminal : P.HasTerminalSource f (code.face code.last) (code.sourceImage (f 0)) := ⟨start, before, tail⟩
  rcases only_two (code.face code.last) target with first | second
  · have member : code.sourceImage (f 0) ∈ P.sourceImages (f 0) F := ⟨⟨code, first⟩, rfl⟩
    refine ⟨chart.firstMotion (code.sourceImage (f 0)), Or.inl ⟨_, member, rfl⟩,
      chart.terminal_from_first f _ ?_⟩
    simpa only [first] using terminal
  · have member : code.sourceImage (f 0) ∈ P.sourceImages (f 0) G := ⟨⟨code, second⟩, rfl⟩
    refine ⟨chart.secondMotion (code.sourceImage (f 0)), Or.inr ⟨_, member, rfl⟩,
      chart.terminal_from_second f _ ?_⟩
    simpa only [second] using terminal

include size small_faces in
theorem small_recoveredSource_mem
    (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves) (different : f 0 ≠ f 1)
    (U : Set Space) (openU : IsOpen U) (targetU : (f 1 : Space) ∈ U)
    (only_two : ∀ H : P.Face, (f 1 : Space) ∈ H.val → H = F ∨ H = G)
    (metric : ∀ x ∈ U ∩ frontier P.body, ∀ y ∈ U ∩ frontier P.body,
      P.surfaceDist x y = dist (chart.unfold x) (chart.unfold y))
    (t : unitInterval) (before : t < 1) (inside : (f t : Space) ∈ U) :
    chart.recoveredSource t f ∈ chart.sourceImages (f 0) := by
  obtain ⟨source, member, terminal⟩ := chart.small_exists_terminal_source size small_faces f geodesic different only_two
  rw [chart.recoveredSource_of_terminal f geodesic source terminal U openU targetU metric t before inside]
  exact member

end EdgeFolding

include size small_faces in
theorem small_geodesic_branch_isolation (f : P.BoundaryCurve) (different : f 0 ≠ f 1)
    (F : P.Face) (unique : ∀ G : P.Face, (f 1 : Space) ∈ G.val → G = F) :
    ∃ W : Set P.BoundaryCurve, IsOpen W ∧ f ∈ W ∧
      ∀ g ∈ W, ∀ h ∈ W, g ∈ P.geodesicCurves → h ∈ P.geodesicCurves →
        g 0 = f 0 → h 0 = f 0 → g 1 = h 1 → g = h := by
  obtain ⟨U, openU, targetU, covers⟩ := P.unique_face_neighborhood F unique
  let path := P.surfacePathOfCurve f
  obtain ⟨t, positive, before, ftU, _⟩ := path.common_time_near_target path U openU targetU
  obtain ⟨V, openV, fV, isolated⟩ := P.recoveredSource_isolation (f 0) F t f
  have evaluation (u : unitInterval) : Continuous (fun g : P.BoundaryCurve => (g u : Space)) :=
    continuous_subtype_val.comp (continuous_eval_const u)
  let W : Set P.BoundaryCurve :=
    (fun g => (g t : Space)) ⁻¹' U ∩ ((fun g => (g 1 : Space)) ⁻¹' U ∩
      ({g | g 0 ≠ g 1} ∩ V))
  have openW : IsOpen W := (openU.preimage (evaluation t)).inter
    ((openU.preimage (evaluation 1)).inter
      ((isClosed_eq (continuous_eval_const 0) (continuous_eval_const 1)).isOpen_compl.inter openV))
  refine ⟨W, openW, ⟨ftU, targetU, different, fV⟩, ?_⟩
  intro g gW h hW geodesic_g geodesic_h source_g source_h target
  have g_inside := (covers _ ⟨gW.1, (g t).property⟩).1
  have h_inside := (covers _ ⟨hW.1, (h t).property⟩).1
  have g_unique := (covers _ ⟨gW.2.1, (g 1).property⟩).2
  have h_unique := (covers _ ⟨hW.2.1, (h 1).property⟩).2
  have g_member : P.recoveredSource F t g ∈ P.sourceImages (f 0) F := by
    simpa only [source_g] using small_recoveredSource_mem size small_faces g geodesic_g gW.2.2.1 F g_unique t before g_inside
  have h_member : P.recoveredSource F t h ∈ P.sourceImages (f 0) F := by
    simpa only [source_h] using small_recoveredSource_mem size small_faces h geodesic_h hW.2.2.1 F h_unique t before h_inside
  have same_source := (isolated g gW.2.2.2 g_member).trans (isolated h hW.2.2.2 h_member).symm
  have same_position := P.recoveredSource_position F t before g h same_source target
  have meet : g t = h t := by
    apply Subtype.ext
    apply dist_eq_zero.mp
    rw [← P.faceCoordinates_rigid F _ g_inside _ h_inside, same_position, dist_self]
  exact small_geodesic_curves_agree_of_meeting size small_faces g h geodesic_g geodesic_h gW.2.2.1
    (source_g.trans source_h.symm) target t positive before meet

include size small_faces in
theorem small_geodesic_branch_isolation_at_edge (f : P.BoundaryCurve) (different : f 0 ≠ f 1)
    (F G : P.Face) (shared : P.ShareEdge F G) (target : (f 1 : Space) ∈ F.val ∩ G.val)
    (not_vertex : (f 1 : Space) ∉ P.vertices) :
    ∃ W : Set P.BoundaryCurve, IsOpen W ∧ f ∈ W ∧
      ∀ g ∈ W, ∀ h ∈ W, g ∈ P.geodesicCurves → h ∈ P.geodesicCurves →
        g 0 = f 0 → h 0 = f 0 → g 1 = h 1 → g = h := by
  obtain ⟨center, inside⟩ := P.solid
  obtain ⟨facets⟩ := P.exists_normalized_facets inside
  obtain ⟨chart⟩ := exists_edge_folding facets F G shared
  obtain ⟨U, openU, targetU, only_two, covers, metric⟩ := chart.exists_metric_neighborhood shared target not_vertex
  let path := P.surfacePathOfCurve f
  obtain ⟨t, positive, before, ftU, _⟩ := path.common_time_near_target path U openU targetU
  obtain ⟨V, openV, fV, isolated⟩ := chart.recoveredSource_isolation (f 0) t f U openU covers ftU targetU
  have evaluation (u : unitInterval) : Continuous (fun g : P.BoundaryCurve => (g u : Space)) :=
    continuous_subtype_val.comp (continuous_eval_const u)
  let W : Set P.BoundaryCurve := (fun g => (g t : Space)) ⁻¹' U ∩
    ((fun g => (g 1 : Space)) ⁻¹' U ∩ ({g | g 0 ≠ g 1} ∩ V))
  have openW : IsOpen W := (openU.preimage (evaluation t)).inter
    ((openU.preimage (evaluation 1)).inter
      ((isClosed_eq (continuous_eval_const 0) (continuous_eval_const 1)).isOpen_compl.inter openV))
  refine ⟨W, openW, ⟨ftU, targetU, different, fV⟩, ?_⟩
  intro g gW h hW hg hh first_g first_h last
  have g_member : chart.recoveredSource t g ∈ chart.sourceImages (f 0) := by
    simpa only [first_g] using chart.small_recoveredSource_mem size small_faces g hg gW.2.2.1 U openU gW.2.1
      (only_two _ gW.2.1) metric t before gW.1
  have h_member : chart.recoveredSource t h ∈ chart.sourceImages (f 0) := by
    simpa only [first_h] using chart.small_recoveredSource_mem size small_faces h hh hW.2.2.1 U openU hW.2.1
      (only_two _ hW.2.1) metric t before hW.1
  have same := (isolated g gW.2.2.2 g_member).trans (isolated h hW.2.2.2 h_member).symm
  have positions := chart.recoveredSource_position t before g h same last
  have meet : g t = h t := by
    apply Subtype.ext
    have equal := congrArg chart.fold.map positions
    rwa [chart.fold_unfold (covers ⟨gW.1, (g t).property⟩), chart.fold_unfold (covers ⟨hW.1, (h t).property⟩)] at equal
  exact small_geodesic_curves_agree_of_meeting size small_faces g h hg hh gW.2.2.1
    (first_g.trans first_h.symm) last t positive before meet

include size small_faces in
theorem small_geodesic_branch_isolation_nonvertex (f : P.BoundaryCurve) (different : f 0 ≠ f 1)
    (not_vertex : (f 1 : Space) ∉ P.vertices) :
    ∃ W : Set P.BoundaryCurve, IsOpen W ∧ f ∈ W ∧
      ∀ g ∈ W, ∀ h ∈ W, g ∈ P.geodesicCurves → h ∈ P.geodesicCurves →
        g 0 = f 0 → h 0 = f 0 → g 1 = h 1 → g = h := by
  rcases P.nonvertex_incident_facets (f 1).property not_vertex with ⟨F, _, unique⟩ | ⟨F, G, shared, target, _⟩
  · exact small_geodesic_branch_isolation size small_faces f different F unique
  · exact small_geodesic_branch_isolation_at_edge size small_faces f different F G shared target not_vertex

include size small_faces in
theorem small_geodesic_count_nearby_nonvertex (a b : frontier P.body) (different : a ≠ b)
    (not_vertex : (b : Space) ∉ P.vertices) :
    ∃ V : Set (frontier P.body), IsOpen V ∧ b ∈ V ∧
      ∀ c ∈ V, Nat.card (P.geodesicFiber a c) ≤ Nat.card (P.geodesicFiber a b) := by
  classical
  let J := P.geodesicFiber a b
  letI : Fintype J := (small_geodesicFiber_finite size small_faces a b different).fintype
  have neighborhoods (f : J) : ∃ W : Set P.BoundaryCurve, IsOpen W ∧ f.val ∈ W ∧
      ∀ g ∈ W, ∀ h ∈ W, g ∈ P.geodesicCurves → h ∈ P.geodesicCurves →
        g 0 = f.val 0 → h 0 = f.val 0 → g 1 = h 1 → g = h := by
    have first : f.val 0 = a := congrArg Prod.fst f.property.2
    have last : f.val 1 = b := congrArg Prod.snd f.property.2
    exact small_geodesic_branch_isolation_nonvertex size small_faces f.val
      (by simpa only [first, last] using different) (by simpa only [last] using not_vertex)
  choose W openW memberW isolated using neighborhoods
  obtain ⟨N, openN, abN, near⟩ := P.geodesic_family_upper_continuous (a, b) (⋃ i : J, W i)
    (isOpen_iUnion openW) (fun f hf ends => mem_iUnion.mpr ⟨⟨f, hf, ends⟩, memberW ⟨f, hf, ends⟩⟩)
  refine ⟨(fun c => (a, c)) ⁻¹' N, openN.preimage (continuous_const.prodMk continuous_id), abN, ?_⟩
  intro c cN
  have covered (g : P.geodesicFiber a c) : ∃ i : J, g.val ∈ W i :=
    mem_iUnion.mp (near g.val g.property.1 (g.property.2 ▸ cN))
  choose index member using covered
  apply Nat.card_le_card_of_injective index
  intro g h equal
  apply Subtype.ext
  have same_branch : h.val ∈ W (index g) := by rw [equal]; exact member h
  exact isolated (index g) g.val (member g) h.val same_branch g.property.1 h.property.1
    ((congrArg Prod.fst g.property.2).trans (congrArg Prod.fst (index g).property.2).symm)
    ((congrArg Prod.fst h.property.2).trans (congrArg Prod.fst (index g).property.2).symm)
    ((congrArg Prod.snd g.property.2).trans (congrArg Prod.snd h.property.2).symm)

include size small_faces in
theorem small_unique_geodesics_nearby_nonvertex (a b : frontier P.body) (different : a ≠ b)
    (not_vertex : (b : Space) ∉ P.vertices) (unique_route : (P.geodesicFiber a b).Subsingleton) :
    ∃ V : Set (frontier P.body), IsOpen V ∧ b ∈ V ∧ ∀ c ∈ V, (P.geodesicFiber a c).Subsingleton := by
  obtain ⟨f, hf⟩ := P.geodesicFiber_nonempty a b
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  obtain ⟨W, openW, fW, isolated⟩ := small_geodesic_branch_isolation_nonvertex size small_faces f
    (by simpa only [first, last] using different) (by simpa only [last] using not_vertex)
  obtain ⟨N, openN, abN, contains⟩ := P.geodesic_family_upper_continuous (a, b) W openW
    (fun g geodesic ends => unique_route ⟨geodesic, ends⟩ hf ▸ fW)
  refine ⟨(fun c => (a, c)) ⁻¹' N, openN.preimage (continuous_const.prodMk continuous_id), abN, ?_⟩
  intro c cN g hg h hh
  exact isolated g (contains g hg.1 (hg.2 ▸ cN)) h (contains h hh.1 (hh.2 ▸ cN)) hg.1 hh.1
    ((congrArg Prod.fst hg.2).trans first.symm) ((congrArg Prod.fst hh.2).trans first.symm)
    ((congrArg Prod.snd hg.2).trans (congrArg Prod.snd hh.2).symm)

include size small_faces in
theorem small_multiple_routes_closed_nonvertex (a b : frontier P.body) (different : a ≠ b)
    (not_vertex : (b : Space) ∉ P.vertices)
    (limit : b ∈ closure {c : frontier P.body | (c : Space) ∈ P.multipleRouteLocus a}) :
    (b : Space) ∈ P.multipleRouteLocus a := by
  rw [P.multiple_routes_iff_fiber a b]
  refine ⟨different, ?_⟩
  intro unique
  obtain ⟨V, openV, bV, unique_near⟩ := small_unique_geodesics_nearby_nonvertex size small_faces a b different not_vertex unique
  obtain ⟨c, cV, multiple⟩ := mem_closure_iff.mp limit V openV bV
  exact ((P.multiple_routes_iff_fiber a c).mp multiple).2 (unique_near c cV)

include size small_faces in
theorem small_closure_multiple_routes_iff_nonvertex (a b : frontier P.body) (different : a ≠ b)
    (not_vertex : (b : Space) ∉ P.vertices) :
    b ∈ closure {c : frontier P.body | (c : Space) ∈ P.multipleRouteLocus a} ↔
      (b : Space) ∈ P.multipleRouteLocus a :=
  ⟨small_multiple_routes_closed_nonvertex size small_faces a b different not_vertex,
    fun member => subset_closure (show b ∈ {c : frontier P.body | (c : Space) ∈ P.multipleRouteLocus a} from member)⟩

include size small_faces in
theorem small_closure_multiple_subset_cutSet (a : frontier P.body) :
    closure {b : frontier P.body | (b : Space) ∈ P.multipleRouteLocus a} ⊆ P.cutSet a := by
  intro b limit
  have different : a ≠ b := by
    rintro rfl
    exact P.source_not_closure_multiple_routes a limit
  by_cases vertex : (b : Space) ∈ P.vertices
  · exact Or.inr ⟨vertex, different.symm⟩
  · exact Or.inl (small_multiple_routes_closed_nonvertex size small_faces a b different vertex limit)

include size small_faces in
theorem small_cutSet_closed (a : frontier P.body) : IsClosed (P.cutSet a) := by
  let vertices : Set (frontier P.body) := {b | (b : Space) ∈ P.vertices ∧ b ≠ a}
  have finite : vertices.Finite :=
    (P.vertices.finite_toSet.preimage (f := fun b : frontier P.body => (b : Space)) Subtype.val_injective.injOn).subset
      (fun _ h => h.1)
  apply isClosed_of_closure_subset
  change closure ({b : frontier P.body | (b : Space) ∈ P.multipleRouteLocus a} ∪ vertices) ⊆ P.cutSet a
  rw [closure_union, finite.isClosed.closure_eq]
  exact union_subset (small_closure_multiple_subset_cutSet size small_faces a) (fun _ member => Or.inr member)

include size small_faces in
theorem small_cutSet_compact (a : frontier P.body) : IsCompact (P.cutSet a) := by
  letI : CompactSpace (frontier P.body) := isCompact_iff_compactSpace.mp
    (P.body_compact.of_isClosed_subset isClosed_frontier P.body_closed.frontier_subset)
  exact (small_cutSet_closed size small_faces a).isCompact

include size small_faces in
theorem small_cutSetInSpace_compact (a : frontier P.body) : IsCompact (P.cutSetInSpace a) :=
  (small_cutSet_compact size small_faces a).image continuous_subtype_val

end SixVertexUnfolding.ConvexPolyhedron
