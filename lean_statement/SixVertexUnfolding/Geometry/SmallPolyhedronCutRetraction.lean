import SixVertexUnfolding.Geometry.SmallPolyhedronTerminalRays
import SixVertexUnfolding.Geometry.CutSetContractible

/-! Continuously extend each ray to its unique cut endpoint. This retracts the
punctured boundary onto the actual cut set and proves it contractible. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter BoundedContinuousFunction
open scoped Topology ENNReal

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
theorem small_cut_endpoints_agree_of_distance_le (a b c d : frontier P.body) (different : a ≠ b)
    (cut_c : c ∈ P.cutSet a) (cut_d : d ∈ P.cutSet a)
    (through_c : c ∈ P.shortestExtensions a b) (through_d : d ∈ P.shortestExtensions a b)
    (ordered : P.surfaceDist a c ≤ P.surfaceDist a d) : c = d := by
  by_cases cut_b : b ∈ P.cutSet a
  · exact (small_shortest_extension_of_cut_point size small_faces a b c cut_b through_c).trans
      (small_shortest_extension_of_cut_point size small_faces a b d cut_b through_d).symm
  obtain ⟨f, hf, s, at_s⟩ := P.shortest_extension_path a b c through_c
  obtain ⟨g, hg, t, at_t⟩ := P.shortest_extension_path a b d through_d
  have f0 : f 0 = a := congrArg Prod.fst hf.2
  have f1 : f 1 = c := congrArg Prod.snd hf.2
  have g0 : g 0 = a := congrArg Prod.fst hg.2
  have g1 : g 1 = d := congrArg Prod.snd hg.2
  have ac : a ≠ c := fun same => P.source_not_cutSet a (same.symm ▸ cut_c)
  have ad : a ≠ d := fun same => P.source_not_cutSet a (same.symm ▸ cut_d)
  have lc : 0 < P.surfaceDist a c := lt_of_le_of_ne (P.surfaceDist_nonneg a c)
    (fun zero => ac (Subtype.ext ((P.surfaceDist_eq_zero_iff a.property c.property).mp zero.symm)))
  have ld : 0 < P.surfaceDist a d := lt_of_le_of_ne (P.surfaceDist_nonneg a d)
    (fun zero => ad (Subtype.ext ((P.surfaceDist_eq_zero_iff a.property d.property).mp zero.symm)))
  let r : unitInterval := ⟨P.surfaceDist a c / P.surfaceDist a d,
    (div_pos lc ld).le, (div_le_one ld).mpr ordered⟩
  have scaled : P.surfaceDist a d * (r : ℝ) = P.surfaceDist a c := by
    dsimp [r]
    field_simp
  have s_positive : 0 < s := lt_of_le_of_ne s.property.1 (by
    intro zero
    have equal : s = 0 := zero.symm
    rw [equal, f0] at at_s
    exact different at_s)
  have s_before : s < 1 := lt_of_le_of_ne s.property.2 (by
    intro one
    have equal : s = 1 := one
    rw [equal, f1] at at_s
    exact cut_b (at_s ▸ cut_c))
  have first_distance := P.geodesic_source_distance f hf.1 s
  have second_distance := P.geodesic_source_distance g hg.1 t
  rw [f0, f1, at_s] at first_distance
  rw [g0, g1, at_t] at second_distance
  have same_time : r * s = t := by
    apply Subtype.ext
    change (r : ℝ) * (s : ℝ) = (t : ℝ)
    apply mul_left_cancel₀ ld.ne'
    calc
      P.surfaceDist a d * ((r : ℝ) * (s : ℝ)) = P.surfaceDist a c * (s : ℝ) := by
        rw [← mul_assoc, scaled]
      _ = P.surfaceDist a d * (t : ℝ) := first_distance.symm.trans second_distance
  have equal := small_same_source_geodesics_agree size small_faces f (P.geodesicPrefix g r)
    hf.1 (P.geodesicPrefix_geodesic g hg.1 r)
    (by simpa only [f0, f1] using ac)
    (by simp only [P.geodesicPrefix_apply, mul_zero, f0, g0])
    (by simp only [P.geodesicPrefix_apply, mul_zero, mul_one]
        rw [P.geodesic_source_distance g hg.1 r, f0, f1, g0, g1, scaled])
    s s_positive s_before (by rw [P.geodesicPrefix_apply, same_time, at_s, at_t])
  have endpoint : c = g r := by
    have value := congrArg (fun h : P.BoundaryCurve => h 1) equal
    simpa only [f1, P.geodesicPrefix_apply, mul_one] using value
  have extends_c := P.geodesic_endpoint_extension g hg.1 r
  rw [g0, g1, ← endpoint] at extends_c
  exact (small_shortest_extension_of_cut_point size small_faces a c d cut_c extends_c).symm

include size small_faces in
/-- Shortest extensions through a point other than the source have a unique cut endpoint. -/
theorem small_cut_endpoint_unique (a b c d : frontier P.body) (different : a ≠ b)
    (cut_c : c ∈ P.cutSet a) (cut_d : d ∈ P.cutSet a)
    (through_c : c ∈ P.shortestExtensions a b) (through_d : d ∈ P.shortestExtensions a b) : c = d := by
  rcases le_total (P.surfaceDist a c) (P.surfaceDist a d) with ordered | ordered
  · exact small_cut_endpoints_agree_of_distance_le size small_faces a b c d different cut_c cut_d through_c through_d ordered
  · exact (small_cut_endpoints_agree_of_distance_le size small_faces a b d c different cut_d cut_c through_d through_c ordered).symm

include size small_faces in
/-- The terminal cut endpoint exists and is unique. -/
theorem small_exists_unique_cut_endpoint (a b : frontier P.body) (different : a ≠ b) :
    ∃! c : frontier P.body, c ∈ P.cutSet a ∧ c ∈ P.shortestExtensions a b := by
  obtain ⟨c, cut, extension⟩ := small_exists_shortest_extension_in_cutSet size small_faces a b different
  exact ⟨c, ⟨cut, extension⟩, fun d hd =>
    small_cut_endpoint_unique size small_faces a b d c different hd.1 cut hd.2 extension⟩

include size small_faces in
/-- Follow the shortest ray to its unique terminal cut point. -/
noncomputable def small_cutEndpoint (a : frontier P.body) (b : {b : frontier P.body // b ≠ a}) : P.cutSet a :=
  ⟨(small_exists_shortest_extension_in_cutSet size small_faces a b.val b.property.symm).choose,
    (small_exists_shortest_extension_in_cutSet size small_faces a b.val b.property.symm).choose_spec.1⟩

include size small_faces in
theorem small_cutEndpoint_extension (a : frontier P.body) (b : {b : frontier P.body // b ≠ a}) :
    (small_cutEndpoint size small_faces a b).val ∈ P.shortestExtensions a b.val :=
  (small_exists_shortest_extension_in_cutSet size small_faces a b.val b.property.symm).choose_spec.2

include size small_faces in
/-- Cut points themselves are fixed by the endpoint map. -/
theorem small_cutEndpoint_fixes (a : frontier P.body) (c : P.cutSet a) :
    small_cutEndpoint size small_faces a ⟨c.val, ne_of_mem_of_not_mem c.property (P.source_not_cutSet a)⟩ = c := by
  apply Subtype.ext
  exact small_shortest_extension_of_cut_point size small_faces a c.val _ c.property
    (small_cutEndpoint_extension size small_faces a _)

include size small_faces in
/-- The terminal endpoint depends continuously on the point being extended. -/
theorem small_cutEndpoint_continuous (a : frontier P.body) : Continuous (small_cutEndpoint size small_faces a) := by
  let X := {b : frontier P.body // b ≠ a}
  let Y := P.cutSet a
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp (small_cutSet_compact size small_faces a)
  let relation : Set (X × Y) := {p | p.2.val ∈ P.shortestExtensions a p.1.val}
  have first : Continuous (fun p : X × Y => p.1.val) := continuous_subtype_val.comp continuous_fst
  have second : Continuous (fun p : X × Y => p.2.val) := continuous_subtype_val.comp continuous_snd
  have closed_relation : IsClosed relation := isClosed_eq
    (P.surfaceDist_continuous.comp (continuous_const.prodMk second))
    ((P.surfaceDist_continuous.comp (continuous_const.prodMk first)).add
      (P.surfaceDist_continuous.comp (first.prodMk second)))
  apply continuous_iff_isClosed.mpr
  intro C closedC
  have equality : (small_cutEndpoint size small_faces a) ⁻¹' C =
      Prod.fst '' (relation ∩ Prod.snd ⁻¹' C) := by
    ext b
    constructor
    · intro member
      exact ⟨(b, small_cutEndpoint size small_faces a b),
        ⟨small_cutEndpoint_extension size small_faces a b, member⟩, rfl⟩
    · rintro ⟨⟨d, c⟩, ⟨extension, member⟩, same⟩
      change d = b at same
      subst d
      have equal : c = small_cutEndpoint size small_faces a b := Subtype.ext
        (small_cut_endpoint_unique size small_faces a b.val c.val _ b.property.symm
          c.property (small_cutEndpoint size small_faces a b).property extension
          (small_cutEndpoint_extension size small_faces a b))
      rwa [equal] at member
  rw [equality]
  exact isClosedMap_fst_of_compactSpace _ (closed_relation.inter (closedC.preimage continuous_snd))

include size small_faces in
theorem small_cutEndpoint_surjective (a : frontier P.body) : Function.Surjective (small_cutEndpoint size small_faces a) := by
  intro c
  exact ⟨⟨c.val, ne_of_mem_of_not_mem c.property (P.source_not_cutSet a)⟩,
    small_cutEndpoint_fixes size small_faces a c⟩

include size small_faces in
/-- The actual vertex-augmented cut set is contractible. -/
theorem small_cutSet_contractible (a : frontier P.body) : ContractibleSpace (P.cutSet a) := by
  let X := {b : frontier P.body // b ≠ a}
  let Y := P.cutSet a
  letI : ContractibleSpace X := P.punctured_boundary_contractible a
  let inclusion : C(Y, X) := ⟨fun c =>
    ⟨c.val, ne_of_mem_of_not_mem c.property (P.source_not_cutSet a)⟩,
    continuous_subtype_val.subtype_mk _⟩
  let retract : C(X, Y) := ⟨small_cutEndpoint size small_faces a, small_cutEndpoint_continuous size small_faces a⟩
  have null := ((id_nullhomotopic X).comp_left inclusion).comp_right retract
  have identity : retract.comp ((ContinuousMap.id X).comp inclusion) = ContinuousMap.id Y := by
    apply ContinuousMap.ext
    intro c
    exact small_cutEndpoint_fixes size small_faces a c
  apply (contractible_iff_id_nullhomotopic Y).mpr
  rwa [identity] at null

include size small_faces in
/-- The embedded graph's spatial trace has this same contractible topology. -/
theorem small_cutSetInSpace_contractible (a : frontier P.body) : ContractibleSpace (P.cutSetInSpace a) := by
  letI : ContractibleSpace (P.cutSet a) := small_cutSet_contractible size small_faces a
  let h : P.cutSet a ≃ₜ P.cutSetInSpace a :=
    Topology.IsEmbedding.subtypeVal.homeomorphImage (P.cutSet a)
  exact h.symm.contractibleSpace

end SixVertexUnfolding.ConvexPolyhedron
