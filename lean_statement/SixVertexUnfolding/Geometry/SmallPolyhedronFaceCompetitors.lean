import SixVertexUnfolding.Geometry.SmallPolyhedronFaceSources
import SixVertexUnfolding.Geometry.ActiveSourceNeighborhoods

/-! Actual face sources give competing surface paths of exactly the developed
length throughout a neighborhood; nearby shortest routes use these sources. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter BoundedContinuousFunction
open scoped Topology ENNReal

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Each actual terminal source is realized by exact-length surface competitors throughout a target neighborhood. -/
theorem small_terminal_source_competitors (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (F : P.Face) (unique_face : ∀ G : P.Face, (f 1 : Space) ∈ G.val → G = F)
    (source : Plane) (terminal : P.HasTerminalSource f F source) :
    ∃ V : Set Space, IsOpen V ∧ (f 1 : Space) ∈ V ∩ F.val ∧ ∀ x ∈ V ∩ F.val,
      ∃ path : P.SurfacePath (f 0) x, path.length ≠ ⊤ ∧ path.length.toReal = dist source (P.faceCoordinates F x) := by
  let path := P.surfacePathOfCurve f
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  obtain ⟨start, start_before, tail⟩ := terminal
  have terminal' : P.HasTerminalSource f F source := ⟨start, start_before, tail⟩
  obtain ⟨O, openO, targetO, covers⟩ := P.unique_face_neighborhood F unique_face
  have near : ∀ᶠ r : ℝ in 𝓝 1, path.curve.extend r ∈ O :=
    path.curve.continuous_extend.continuousAt.eventually (openO.mem_nhds (by simpa using targetO))
  have late : ∀ᶠ r : ℝ in 𝓝 1, (start : ℝ) < r := Ioi_mem_nhds start_before
  obtain ⟨r, before, after, inO⟩ := (late.and near).exists_lt
  let m : unitInterval := ⟨r, (start.property.1.trans_lt after).le, before.le⟩
  have positive : 0 < m := start.property.1.trans_lt after
  have fmO : (f m : Space) ∈ O := by
    change path.curve.extend (m : ℝ) ∈ O at inO
    rw [Path.extend_apply path.curve m.property] at inO
    exact inO
  have unique_m := (covers _ ⟨fmO, (f m).property⟩).2
  have distinct_m : f 0 ≠ f m := by
    intro same
    exact positive.ne ((path.shortest_lipschitz_injective
      (fun h => different (Subtype.ext h)) shortest finite speed) (congrArg Subtype.val same))
  have prefix_unique := small_geodesic_interior_targets_unique size small_faces f geodesic different m before
  obtain ⟨other, _, U, openU, fmU, formula⟩ := small_unique_route_source_distance size small_faces
    (f 0) (f m) distinct_m F unique_m prefix_unique
  have same := P.local_formula_identifies_source f geodesic F source other terminal' start tail
    m after.le positive before U openU fmU formula
  subst other
  have at_m := tail m ⟨after.le, before.le⟩
  exact P.source_formula_extension (f 0).property F at_m.1 terminal'.target_in_face unique_m source m
    positive before at_m.2 U openU fmU formula

include size small_faces in
/-- All active source copies simultaneously give actual exact-length competitors nearby. -/
theorem small_active_source_competitors (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ ∀ x ∈ V ∩ F.val,
      ∀ source ∈ P.activeSources a b F, ∃ path : P.SurfacePath a x,
        path.length ≠ ⊤ ∧ path.length.toReal = dist source (P.faceCoordinates F x) := by
  classical
  let S := P.activeSources a b F
  letI : Fintype S := (small_activeSources_finite size small_faces a b different F unique_face).fintype
  have neighborhoods (source : S) : ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧
      ∀ x ∈ V ∩ F.val, ∃ path : P.SurfacePath a x,
        path.length ≠ ⊤ ∧ path.length.toReal = dist source.val (P.faceCoordinates F x) := by
    obtain ⟨f, hf, terminal⟩ := source.property
    have first : f 0 = a := congrArg Prod.fst hf.2
    have last : f 1 = b := congrArg Prod.snd hf.2
    obtain ⟨V, openV, bV, competitors⟩ := small_terminal_source_competitors size small_faces f hf.1
      (by simpa only [first, last] using different) F (by simpa only [last] using unique_face) source terminal
    refine ⟨V, openV, by simpa only [last] using bV.1, ?_⟩
    intro x hx
    obtain ⟨path, finite, length⟩ := competitors x hx
    exact ⟨path.cast (congrArg Subtype.val first).symm rfl, finite, length⟩
  choose V openV bV competitors using neighborhoods
  refine ⟨⋂ source : S, V source, isOpen_iInter_of_finite openV, mem_iInter.mpr bV, ?_⟩
  intro x hx source active
  exact competitors ⟨source, active⟩ x ⟨mem_iInter.mp hx.1 ⟨source, active⟩, hx.2⟩

include size small_faces in
/-- Every nearby intrinsic distance is attained by one of the original target's active source formulas. -/
theorem small_active_source_distance_nearby (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ ∀ x ∈ V ∩ frontier P.body,
      ∃ source ∈ P.activeSources a b F, P.surfaceDist a x = dist source (P.faceCoordinates F x) := by
  classical
  let J := P.geodesicFiber a b
  have neighborhoods (f : J) : ∃ source : Plane, P.HasTerminalSource f.val F source ∧
      ∃ W : Set P.BoundaryCurve, IsOpen W ∧ f.val ∈ W ∧
      ∀ g ∈ W, g ∈ P.geodesicCurves → g 0 = a →
        P.surfaceDist (g 0) (g 1) = dist source (P.faceCoordinates F (g 1)) := by
    have first : f.val 0 = a := congrArg Prod.fst f.property.2
    have last : f.val 1 = b := congrArg Prod.snd f.property.2
    obtain ⟨source, _, terminal, W, openW, fW, formula⟩ := small_geodesic_branch_distance size small_faces f.val f.property.1
      (by simpa only [first, last] using different) F (by simpa only [last] using unique_face)
    exact ⟨source, terminal, W, openW, fW, fun g hg geo first_g => formula g hg geo (first_g.trans first.symm)⟩
  choose source terminal W openW memberW formula using neighborhoods
  obtain ⟨N, openN, abN, near⟩ := P.geodesic_family_upper_continuous (a, b) (⋃ i : J, W i)
    (isOpen_iUnion openW) (fun f hf ends => mem_iUnion.mpr ⟨⟨f, hf, ends⟩, memberW ⟨f, hf, ends⟩⟩)
  let V : Set (frontier P.body) := (fun c => (a, c)) ⁻¹' N
  have openV : IsOpen V := openN.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨U, openU, sameU⟩ := isOpen_induced_iff.mp openV
  refine ⟨U, openU, ?_, ?_⟩
  · have bV : b ∈ V := abN
    rw [← sameU] at bV
    exact bV
  · intro x hx
    let c : frontier P.body := ⟨x, hx.2⟩
    have cV : c ∈ V := sameU ▸ hx.1
    obtain ⟨g, hg⟩ := P.geodesicFiber_nonempty a c
    obtain ⟨i, gi⟩ := mem_iUnion.mp (near g hg.1 (hg.2 ▸ cV))
    have first : g 0 = a := congrArg Prod.fst hg.2
    have last : g 1 = c := congrArg Prod.snd hg.2
    refine ⟨source i, ⟨i.val, i.property, terminal i⟩, ?_⟩
    simpa only [first, last] using formula i g gi hg.1 first

end SixVertexUnfolding.ConvexPolyhedron
