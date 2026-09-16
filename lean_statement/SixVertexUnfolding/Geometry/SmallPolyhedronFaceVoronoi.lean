import SixVertexUnfolding.Geometry.SmallPolyhedronFaceCompetitors
import SixVertexUnfolding.Geometry.FaceLineCutPersistence

/-! Near a face-interior target, the actual cut locus equals the finite Voronoi
boundary of its active sources. This yields persistence along straight lines. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter BoundedContinuousFunction
open scoped Topology ENNReal

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- On a face neighborhood, intrinsic distance is exactly the minimum over the old target's active sources. -/
theorem small_local_minimum_distance (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ ∀ x ∈ V ∩ F.val,
      (∀ source ∈ P.activeSources a b F, P.surfaceDist a x ≤ dist source (P.faceCoordinates F x)) ∧
      ∃ source ∈ P.activeSources a b F, P.surfaceDist a x = dist source (P.faceCoordinates F x) := by
  obtain ⟨U, openU, bU, competitors⟩ := small_active_source_competitors size small_faces a b different F unique_face
  obtain ⟨W, openW, bW, selection⟩ := small_active_source_distance_nearby size small_faces a b different F unique_face
  refine ⟨U ∩ W, openU.inter openW, ⟨bU, bW⟩, ?_⟩
  intro x hx
  refine ⟨?_, selection x ⟨hx.1.2, F.subset_frontier hx.2⟩⟩
  intro source active
  obtain ⟨path, finite, length⟩ := competitors x ⟨hx.1.1, hx.2⟩ source active
  calc
    P.surfaceDist a x ≤ path.length.toReal := ENNReal.toReal_mono finite path.surfaceEDist_le_length
    _ = dist source (P.faceCoordinates F x) := length

include size small_faces in
/-- The same formula as a least-element statement, with finiteness and nonemptiness explicit. -/
theorem small_finite_local_minimum_distance (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    (P.activeSources a b F).Finite ∧ (P.activeSources a b F).Nonempty ∧
      ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ ∀ x ∈ V ∩ F.val,
        IsLeast ((fun source => dist source (P.faceCoordinates F x)) '' P.activeSources a b F)
          (P.surfaceDist a x) := by
  obtain ⟨V, openV, bV, formula⟩ := small_local_minimum_distance size small_faces a b different F unique_face
  refine ⟨small_activeSources_finite size small_faces a b different F unique_face,
    small_activeSources_nonempty size small_faces a b different F unique_face, V, openV, bV, ?_⟩
  intro x hx
  obtain ⟨lower, source, active, equal⟩ := formula x hx
  refine ⟨⟨source, active, equal.symm⟩, ?_⟩
  rintro _ ⟨other, member, rfl⟩
  exact lower other member

include size small_faces in
/-- A local planar source-distance formula forces the actual shortest route to be unique. -/
theorem small_unique_route_of_local_source_formula (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F)
    (source : Plane) (U : Set Space) (openU : IsOpen U) (bU : (b : Space) ∈ U)
    (formula : ∀ x ∈ U ∩ frontier P.body, P.surfaceDist a x = dist source (P.faceCoordinates F x)) :
    (P.geodesicFiber a b).Subsingleton := by
  intro f hf g hg
  obtain ⟨first, hs, fs, cs, first_eq⟩ := P.geodesicFiber_path a b f hf
  obtain ⟨second, ht, ft, ct, second_eq⟩ := P.geodesicFiber_path a b g hg
  obtain ⟨V, openV, bV, in_face⟩ := P.unique_face_neighborhood F unique_face
  have agree := first.agree_of_terminal_distance_formula second hs ht fs ft cs ct
    (small_shortest_lipschitz_avoids_vertices size small_faces first
      (fun h => different (Subtype.ext h)) hs fs cs) F source (U ∩ V) (openU.inter openV) ⟨bU, bV⟩
    (fun _ hx => (in_face _ ⟨hx.1.2, hx.2⟩).1) (fun _ hx => formula _ ⟨hx.1.1, hx.2⟩)
  rw [← first_eq, ← second_eq, first.eq_of_curve_eq second agree]

include size small_faces in
/-- Route uniqueness is exactly the existence of a local single-source formula. -/
theorem small_unique_route_iff_local_source_formula (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    (P.geodesicFiber a b).Subsingleton ↔
      ∃ source : Plane, ∃ U : Set Space, IsOpen U ∧ (b : Space) ∈ U ∧
        ∀ x ∈ U ∩ frontier P.body, P.surfaceDist a x = dist source (P.faceCoordinates F x) := by
  constructor
  · intro unique
    obtain ⟨source, _, U, openU, bU, formula⟩ := small_unique_route_source_distance size small_faces a b different F unique_face unique
    exact ⟨source, U, openU, bU, formula⟩
  · rintro ⟨source, U, openU, bU, formula⟩
    exact small_unique_route_of_local_source_formula size small_faces a b different F unique_face source U openU bU formula

include size small_faces in
/-- A finite minimum formula detects route uniqueness without treating unused source copies as admissible. -/
theorem small_unique_route_iff_unique_minimum (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (bF : (b : Space) ∈ F.val) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F)
    (sources : Set Plane) (finite : sources.Finite)
    (V : Set Space) (openV : IsOpen V) (bV : (b : Space) ∈ V)
    (minimum : ∀ x ∈ V ∩ F.val,
      (∀ source ∈ sources, P.surfaceDist a x ≤ dist source (P.faceCoordinates F x)) ∧
      ∃ source ∈ sources, P.surfaceDist a x = dist source (P.faceCoordinates F x)) :
    (P.geodesicFiber a b).Subsingleton ↔
      {source ∈ sources | dist source (P.faceCoordinates F b) = P.surfaceDist a b}.Subsingleton := by
  classical
  constructor
  · intro unique
    obtain ⟨actual, _, U, openU, bU, formula⟩ :=
      small_unique_route_source_distance size small_faces a b different F unique_face unique
    have identifies (source : Plane) (member : source ∈ sources)
        (attains : dist source (P.faceCoordinates F b) = P.surfaceDist a b) : actual = source := by
      apply P.local_face_source_comparison_eq F b bF unique_face actual source (U ∩ V)
        (openU.inter openV) ⟨bU, bV⟩
      · intro x hx
        rw [← formula x ⟨hx.1.1, F.subset_frontier hx.2⟩]
        exact (minimum x ⟨hx.1.2, hx.2⟩).1 source member
      · rw [← formula b ⟨bU, b.property⟩, attains]
    intro p hp q hq
    exact (identifies p hp.1 hp.2).symm.trans (identifies q hq.1 hq.2)
  · intro unique
    letI : Fintype sources := finite.fintype
    obtain ⟨p, member, at_b⟩ := (minimum b ⟨bV, bF⟩).2
    let S := V ∩ F.val
    let formulas (q : sources) (x : Space) := dist q.val (P.faceCoordinates F x)
    have selected (x : Space) (hx : x ∈ S) : ∃ q : sources, P.surfaceDist a x = formulas q x := by
      obtain ⟨q, hq, equal⟩ := (minimum x hx).2
      exact ⟨⟨q, hq⟩, equal⟩
    have separated (q : sources) (distinct : q ≠ ⟨p, member⟩) : formulas ⟨p, member⟩ b ≠ formulas q b := by
      intro equal
      apply distinct
      apply Subtype.ext
      exact unique ⟨q.property, equal.symm.trans at_b.symm⟩ ⟨member, at_b.symm⟩
    obtain ⟨W, openW, bW, formula⟩ := continuous_finite_choice_local S (P.surfaceDist a) formulas
      ((P.surfaceDist_continuousOn a.property).mono (fun _ hx => F.subset_frontier hx.2))
      (fun q => (continuous_const.dist (P.faceCoordinates F).continuous_of_finiteDimensional).continuousOn)
      selected b ⟨bV, bF⟩ ⟨p, member⟩ at_b separated
    obtain ⟨O, openO, bO, face⟩ := P.unique_face_neighborhood F unique_face
    apply small_unique_route_of_local_source_formula size small_faces a b different F unique_face p
      ((W ∩ V) ∩ O) ((openW.inter openV).inter openO) ⟨⟨bW, bV⟩, bO⟩
    intro x hx
    exact formula x ⟨hx.1.1.1, hx.1.1.2, (face _ ⟨hx.1.2, hx.2⟩).1⟩

include size small_faces in
/-- Near a distinct target in one face, multiple shortest routes are exactly ties between nearest active sources. -/
theorem small_local_voronoi_cut_locus (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ ∀ x ∈ V ∩ F.val,
      (x ∈ P.multipleRouteLocus a ↔ P.faceCoordinates F x ∈ voronoiBoundary (P.activeSources a b F)) := by
  obtain ⟨U, openU, bU, minimum⟩ := small_local_minimum_distance size small_faces a b different F unique_face
  obtain ⟨O, openO, bO, face⟩ := P.unique_face_neighborhood F unique_face
  let V := (U ∩ O) ∩ ({(a : Space)}ᶜ : Set Space)
  refine ⟨V, (openU.inter openO).inter isClosed_singleton.isOpen_compl,
    ⟨⟨bU, bO⟩, fun same => different (Subtype.ext same.symm)⟩, ?_⟩
  intro x hx
  let c : frontier P.body := ⟨x, F.subset_frontier hx.2⟩
  have distinct_c : a ≠ c := fun same => hx.1.2 (congrArg Subtype.val same.symm)
  have unique_c := (face x ⟨hx.1.1.2, c.property⟩).2
  have criterion := small_unique_route_iff_unique_minimum size small_faces a c distinct_c F hx.2 unique_c
    (P.activeSources a b F) (small_activeSources_finite size small_faces a b different F unique_face)
    U openU hx.1.1.1 minimum
  have value := minimum x ⟨hx.1.1.1, hx.2⟩
  have ties := mem_voronoiBoundary_iff_multiple_minima (P.activeSources a b F) (P.faceCoordinates F x)
    (P.surfaceDist a x) value.1 value.2
  change (c : Space) ∈ P.multipleRouteLocus a ↔ _
  rw [P.multiple_routes_iff_fiber a c, and_iff_right distinct_c]
  exact criterion.not.trans ties.symm

include size small_faces in
theorem small_face_cut_persists_along_line (a : frontier P.body) (F : P.Face)
    (curve : ℝ →ᵃ[ℝ] Space) {t : ℝ} (target : curve t ∈ F.val)
    (unique : ∀ G : P.Face, curve t ∈ G.val → G = F)
    (cut : curve t ∈ P.multipleRouteLocus a)
    (regular : t ∉ lineSourceCrossings (P.sourceImages a F) ((P.faceCoordinates F).comp curve)) :
    ∃ J : Set ℝ, IsOpen J ∧ t ∈ J ∧ ∀ s ∈ J, curve s ∈ F.val → curve s ∈ P.multipleRouteLocus a := by
  let b : frontier P.body := ⟨curve t, F.subset_frontier target⟩
  have different : a ≠ b := ((P.multiple_routes_iff_fiber a b).mp cut).1
  obtain ⟨V, openV, bV, diagram⟩ := small_local_voronoi_cut_locus size small_faces a b different F unique
  have contained := small_activeSources_subset size small_faces a b different F unique
  have common (p : Plane) (hp : p ∈ P.activeSources a b F) (q : Plane) (hq : q ∈ P.activeSources a b F) :
      dist p (((P.faceCoordinates F).comp curve) t) = dist q (((P.faceCoordinates F).comp curve) t) :=
    (P.activeSource_distance a b F p hp).symm.trans (P.activeSource_distance a b F q hq)
  have all_tied := voronoi_ties_persist_on_line (P.sourceImages a F) (P.activeSources a b F)
    contained ((P.faceCoordinates F).comp curve) regular common ((diagram _ ⟨bV, target⟩).mp cut)
  exact ⟨curve ⁻¹' V, openV.preimage curve.continuous_of_finiteDimensional, bV,
    fun s hs in_face => (diagram _ ⟨hs, in_face⟩).mpr (all_tied s)⟩

end SixVertexUnfolding.ConvexPolyhedron
