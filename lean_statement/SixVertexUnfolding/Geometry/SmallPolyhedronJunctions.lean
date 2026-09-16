import SixVertexUnfolding.Geometry.SmallPolyhedronFaceSources
import SixVertexUnfolding.Geometry.SmallPolyhedronEdgeSources
import SixVertexUnfolding.Geometry.FiniteJunctions
import SixVertexUnfolding.Geometry.RegularCutPoints

/-! Actual shortest routes correspond to distinct active source copies. Finite
source lists give finitely many junctions, including along original edges. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter BoundedContinuousFunction
open scoped Topology ENNReal

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Two geodesics with the same endpoints and terminal source are the same route. -/
theorem small_routes_agree_of_terminal_source (f g : P.BoundaryCurve)
    (hf : f ∈ P.geodesicCurves) (hg : g ∈ P.geodesicCurves) (different : f 0 ≠ f 1)
    (first : f 0 = g 0) (last : f 1 = g 1) (F : P.Face) (source : Plane)
    (left : P.HasTerminalSource f F source) (right : P.HasTerminalSource g F source) : f = g := by
  obtain ⟨s, s_before, left⟩ := left
  obtain ⟨u, u_before, right⟩ := right
  obtain ⟨t, after, before⟩ := exists_between (max_lt s_before u_before)
  have left_t := left t ⟨(le_max_left s u).trans after.le, before.le⟩
  have right_t := right t ⟨(le_max_right s u).trans after.le, before.le⟩
  have coordinates : P.faceCoordinates F (f t) = P.faceCoordinates F (g t) := by
    rw [left_t.2, right_t.2, last]
  have meet : f t = g t := by
    apply Subtype.ext
    apply dist_eq_zero.mp
    rw [← P.faceCoordinates_rigid F _ left_t.1 _ right_t.1, coordinates, dist_self]
  exact small_geodesic_curves_agree_of_meeting size small_faces f g hf hg different first last t
    ((unitInterval.nonneg s).trans_lt ((le_max_left s u).trans_lt after)) before meet

include size small_faces in
/-- Active source copies are in bijection with actual normalized shortest routes. -/
theorem small_routes_equiv_active_sources (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    Nonempty (P.geodesicFiber a b ≃ P.activeSources a b F) := by
  classical
  have sources (f : P.geodesicFiber a b) : ∃ source, P.HasTerminalSource f.val F source := by
    have first : f.val 0 = a := congrArg Prod.fst f.property.2
    have last : f.val 1 = b := congrArg Prod.snd f.property.2
    obtain ⟨source, _, terminal⟩ := small_exists_terminal_source size small_faces f.val f.property.1
      (by simpa only [first, last] using different) F (by simpa only [last] using unique_face)
    exact ⟨source, terminal⟩
  choose source terminal using sources
  let code (f : P.geodesicFiber a b) : P.activeSources a b F := ⟨source f, f.val, f.property, terminal f⟩
  have injective : Function.Injective code := by
    intro f g equal
    apply Subtype.ext
    have first : f.val 0 = a := congrArg Prod.fst f.property.2
    have last : f.val 1 = b := congrArg Prod.snd f.property.2
    apply small_routes_agree_of_terminal_source size small_faces f.val g.val f.property.1 g.property.1
      (by simpa only [first, last] using different)
      ((congrArg Prod.fst f.property.2).trans (congrArg Prod.fst g.property.2).symm)
      ((congrArg Prod.snd f.property.2).trans (congrArg Prod.snd g.property.2).symm) F (source f) (terminal f)
    have same : source f = source g := congrArg Subtype.val equal
    rw [same]
    exact terminal g
  have surjective : Function.Surjective code := by
    intro q
    obtain ⟨f, hf, actual⟩ := q.property
    refine ⟨⟨f, hf⟩, Subtype.ext ?_⟩
    exact (terminal ⟨f, hf⟩).unique actual
  exact ⟨Equiv.ofBijective code ⟨injective, surjective⟩⟩

include size small_faces in
/-- The finite active-source set has exactly as many elements as the route fiber. -/
theorem small_activeSources_ncard (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    (P.activeSources a b F).ncard = Nat.card (P.geodesicFiber a b) := by
  obtain ⟨equiv⟩ := small_routes_equiv_active_sources size small_faces a b different F unique_face
  exact (Nat.card_congr equiv).symm

include size small_faces in
/-- Only finitely many interior-face targets admit three or more shortest routes. -/
theorem small_face_junctions_finite (a : frontier P.body) (F : P.Face) :
    {b : frontier P.body | a ≠ b ∧ (∀ G : P.Face, (b : Space) ∈ G.val → G = F) ∧
      2 < Nat.card (P.geodesicFiber a b)}.Finite := by
  let junctions : Set (frontier P.body) := {b | a ≠ b ∧
    (∀ G : P.Face, (b : Space) ∈ G.val → G = F) ∧ 2 < Nat.card (P.geodesicFiber a b)}
  have image_finite : ((fun b : frontier P.body => P.faceCoordinates F b) '' junctions).Finite := by
    apply (finite_three_site_centers (P.sourceImages a F) (P.sourceImages_finite a F)).subset
    rintro _ ⟨b, hb, rfl⟩
    have count : 2 < (P.activeSources a b F).ncard := by
      rw [small_activeSources_ncard size small_faces a b hb.1 F hb.2.1]
      exact hb.2.2
    obtain ⟨p, hp, q, hq, r, hr, pq, pr, qr⟩ :=
      (two_lt_ncard (small_activeSources_finite size small_faces a b hb.1 F hb.2.1)).mp count
    have subset := small_activeSources_subset size small_faces a b hb.1 F hb.2.1
    have pvalue := P.activeSource_distance a b F p hp
    exact ⟨p, subset hp, q, subset hq, r, subset hr, pq, pr, qr,
      pvalue.symm.trans (P.activeSource_distance a b F q hq),
      pvalue.symm.trans (P.activeSource_distance a b F r hr)⟩
  apply image_finite.of_finite_image
  intro b hb c hc same
  have in_face (x : frontier P.body) (hx : x ∈ junctions) : (x : Space) ∈ F.val := by
    obtain ⟨G, member⟩ := P.boundary_point_in_face x.property
    simpa only [hx.2.1 G member] using member
  apply Subtype.ext
  apply dist_eq_zero.mp
  change P.faceCoordinates F b = P.faceCoordinates F c at same
  rw [← P.faceCoordinates_rigid F _ (in_face b hb) _ (in_face c hc), same, dist_self]

include size small_faces in
/-- A whole original edge contains only finitely many nonvertex junctions. -/
theorem small_edge_junctions_finite (a : frontier P.body) (F G : P.Face)
    (shared : P.ShareEdge F G) :
    {b : frontier P.body | a ≠ b ∧ (b : Space) ∈ F.val ∩ G.val ∧
      (b : Space) ∉ P.vertices ∧ 2 < Nat.card (P.geodesicFiber a b)}.Finite := by
  obtain ⟨center, inside⟩ := P.solid
  obtain ⟨facets⟩ := P.exists_normalized_facets inside
  obtain ⟨chart⟩ := exists_edge_folding facets F G shared
  let junctions : Set (frontier P.body) := {b | a ≠ b ∧ (b : Space) ∈ F.val ∩ G.val ∧
    (b : Space) ∉ P.vertices ∧ 2 < Nat.card (P.geodesicFiber a b)}
  have image_finite : ((fun b : frontier P.body => chart.unfold b) '' junctions).Finite := by
    apply (finite_three_site_centers (chart.sourceImages a) (chart.sourceImages_finite a)).subset
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨patch⟩ := chart.exists_metric_patch shared hb.2.1 hb.2.2.1
    have count : 2 < (chart.activeSources a b).ncard := by
      rw [patch.small_activeSources_ncard size small_faces a b hb.1 patch.center_mem]
      exact hb.2.2.2
    obtain ⟨p, hp, q, hq, r, hr, pq, pr, qr⟩ :=
      (two_lt_ncard (patch.small_activeSources_finite size small_faces a b hb.1 patch.center_mem)).mp count
    have subset := patch.small_activeSources_subset size small_faces a b hb.1 patch.center_mem
    have pvalue := chart.activeSource_distance patch a b patch.center_mem p hp
    exact ⟨p, subset hp, q, subset hq, r, subset hr, pq, pr, qr,
      pvalue.symm.trans (chart.activeSource_distance patch a b patch.center_mem q hq),
      pvalue.symm.trans (chart.activeSource_distance patch a b patch.center_mem r hr)⟩
  apply image_finite.of_finite_image
  intro b hb c hc same
  apply Subtype.ext
  change chart.unfold b = chart.unfold c at same
  have equal := congrArg chart.fold.map same
  rwa [chart.fold_unfold (Or.inl hb.2.1.1), chart.fold_unfold (Or.inl hc.2.1.1)] at equal

include size small_faces in
/-- Finite route counts detect the explicitly defined junctions. -/
theorem small_junction_iff_route_count (a b : frontier P.body) (different : a ≠ b) :
    b ∈ P.junctions a ↔ 2 < Nat.card (P.geodesicFiber a b) := by
  change (a ≠ b ∧ ∃ f ∈ P.geodesicFiber a b, ∃ g ∈ P.geodesicFiber a b,
    ∃ h ∈ P.geodesicFiber a b, f ≠ g ∧ f ≠ h ∧ g ≠ h) ↔ _
  rw [and_iff_right different]
  exact (two_lt_ncard (small_geodesicFiber_finite size small_faces a b different)).symm

include size small_faces in
/-- There are only finitely many targets with three or more shortest routes, on the entire surface. -/
theorem small_junctions_finite (a : frontier P.body) : (P.junctions a).Finite := by
  let face_targets (F : P.Face) : Set (frontier P.body) :=
    {b | a ≠ b ∧ (∀ G : P.Face, (b : Space) ∈ G.val → G = F) ∧
      2 < Nat.card (P.geodesicFiber a b)}
  let edge_targets (e : {pair : P.Face × P.Face // P.ShareEdge pair.1 pair.2}) : Set (frontier P.body) :=
    {b | a ≠ b ∧ (b : Space) ∈ e.val.1.val ∩ e.val.2.val ∧
      (b : Space) ∉ P.vertices ∧ 2 < Nat.card (P.geodesicFiber a b)}
  have faces_finite : (⋃ F, face_targets F).Finite :=
    finite_iUnion (fun F => small_face_junctions_finite size small_faces a F)
  have edges_finite : (⋃ e, edge_targets e).Finite :=
    finite_iUnion (fun e => small_edge_junctions_finite size small_faces a e.val.1 e.val.2 e.property)
  have vertices_finite := P.vertices.finite_toSet.preimage
    (f := fun b : frontier P.body => (b : Space)) Subtype.val_injective.injOn
  apply ((faces_finite.union edges_finite).union vertices_finite).subset
  intro b hb
  have count := (small_junction_iff_route_count size small_faces a b hb.1).mp hb
  by_cases vertex : (b : Space) ∈ P.vertices
  · exact Or.inr vertex
  · apply Or.inl
    rcases P.nonvertex_incident_facets b.property vertex with
      ⟨F, _, unique⟩ | ⟨F, G, shared, target, _⟩
    · exact Or.inl (mem_iUnion.mpr ⟨F, hb.1, unique, count⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨(F, G), shared⟩, hb.1, target, vertex, count⟩)

include size small_faces in
theorem small_cutExceptions_finite (a : frontier P.body) : (P.cutExceptions a).Finite := by
  have vertices_finite := P.vertices.finite_toSet.preimage
    (f := fun b : frontier P.body => (b : Space)) Subtype.val_injective.injOn
  exact (small_junctions_finite size small_faces a).union (vertices_finite.subset (fun _ h => h.1))

end SixVertexUnfolding.ConvexPolyhedron
