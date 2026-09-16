import SixVertexUnfolding.Geometry.SmallPolyhedronRoutePrefixes
import SixVertexUnfolding.Geometry.UniqueRouteSourceDistance
import SixVertexUnfolding.Geometry.ActiveSources

/-! Actual terminal source copies in a face, and their stability under changes
of target. These are sources of actual routes, not merely candidate images. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter BoundedContinuousFunction
open scoped Topology ENNReal

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Every geodesic ending in a unique face has an actual terminal source in the fixed finite list. -/
theorem small_exists_terminal_source (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (F : P.Face) (unique_face : ∀ G : P.Face, (f 1 : Space) ∈ G.val → G = F) :
    ∃ source ∈ P.sourceImages (f 0) F, P.HasTerminalSource f F source := by
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  obtain ⟨code, start, before, tail⟩ := (P.surfacePathOfCurve f).exists_terminal_source_code shortest finite speed
    (small_shortest_lipschitz_avoids_vertices size small_faces _ (fun h => different (Subtype.ext h)) shortest finite speed)
  have target : (f 1 : Space) ∈ (code.face code.last).val := (tail 1 ⟨unitInterval.le_one', le_rfl⟩).1
  have same := unique_face (code.face code.last) target
  refine ⟨code.sourceImage (f 0), ⟨⟨code, same⟩, rfl⟩, start, before, ?_⟩
  intro t ht
  simpa only [same] using tail t ht

include size small_faces in
/-- Every active source is one of the finitely many developed face-sequence candidates. -/
theorem small_activeSources_subset (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    P.activeSources a b F ⊆ P.sourceImages a F := by
  rintro source ⟨f, hf, terminal⟩
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  obtain ⟨other, member, actual⟩ := small_exists_terminal_source size small_faces f hf.1
    (by simpa only [first, last] using different) F (by simpa only [last] using unique_face)
  rw [terminal.unique actual]
  simpa only [first] using member

include size small_faces in
/-- Only finitely many actual source copies occur at an interior-face target. -/
theorem small_activeSources_finite (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    (P.activeSources a b F).Finite :=
  (P.sourceImages_finite a F).subset (small_activeSources_subset size small_faces a b different F unique_face)

include size small_faces in
/-- At least one actual source copy occurs at an interior-face target. -/
theorem small_activeSources_nonempty (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    (P.activeSources a b F).Nonempty := by
  obtain ⟨f, hf⟩ := P.geodesicFiber_nonempty a b
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  obtain ⟨source, _, terminal⟩ := small_exists_terminal_source size small_faces f hf.1
    (by simpa only [first, last] using different) F (by simpa only [last] using unique_face)
  exact ⟨source, f, hf, terminal⟩

include size small_faces in
/-- Around one route, every nearby route from the same source uses its fixed planar distance formula. -/
theorem small_geodesic_branch_distance (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (F : P.Face) (unique : ∀ G : P.Face, (f 1 : Space) ∈ G.val → G = F) :
    ∃ source ∈ P.sourceImages (f 0) F, P.HasTerminalSource f F source ∧
      ∃ W : Set P.BoundaryCurve, IsOpen W ∧ f ∈ W ∧
      ∀ g ∈ W, g ∈ P.geodesicCurves → g 0 = f 0 →
        P.surfaceDist (g 0) (g 1) = dist source (P.faceCoordinates F (g 1)) := by
  obtain ⟨U, openU, targetU, covers⟩ := P.unique_face_neighborhood F unique
  let path := P.surfacePathOfCurve f
  obtain ⟨t, _, before, ftU, _⟩ := path.common_time_near_target path U openU targetU
  obtain ⟨V, openV, fV, isolated⟩ := P.recoveredSource_isolation (f 0) F t f
  have evaluation (u : unitInterval) : Continuous (fun g : P.BoundaryCurve => (g u : Space)) :=
    continuous_subtype_val.comp (continuous_eval_const u)
  let W : Set P.BoundaryCurve :=
    (fun g => (g t : Space)) ⁻¹' U ∩ ((fun g => (g 1 : Space)) ⁻¹' U ∩ ({g | g 0 ≠ g 1} ∩ V))
  have openW : IsOpen W := (openU.preimage (evaluation t)).inter
    ((openU.preimage (evaluation 1)).inter
      ((isClosed_eq (continuous_eval_const 0) (continuous_eval_const 1)).isOpen_compl.inter openV))
  obtain ⟨actual, _, terminal⟩ := small_exists_terminal_source size small_faces f geodesic different F unique
  have same := terminal.recovered_eq geodesic t before (covers _ ⟨ftU, (f t).property⟩).1
  have recovered_terminal : P.HasTerminalSource f F (P.recoveredSource F t f) := by rw [same]; exact terminal
  refine ⟨P.recoveredSource F t f, small_recoveredSource_mem size small_faces f geodesic different F unique t before
    (covers _ ⟨ftU, (f t).property⟩).1, recovered_terminal, W, openW, ⟨ftU, targetU, different, fV⟩, ?_⟩
  intro g near shortest same_start
  have inside := (covers _ ⟨near.1, (g t).property⟩).1
  have target := covers _ ⟨near.2.1, (g 1).property⟩
  have member : P.recoveredSource F t g ∈ P.sourceImages (f 0) F := by
    simpa only [same_start] using small_recoveredSource_mem size small_faces g shortest near.2.2.1 F target.2 t before inside
  rw [P.recoveredSource_distance g shortest F t before inside target.1, isolated g near.2.2.2 member]

include size small_faces in
/-- Actual route uniqueness suffices for a local source-distance formula; candidate-distance ties are allowed. -/
theorem small_unique_route_source_distance (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F)
    (unique_route : (P.geodesicFiber a b).Subsingleton) :
    ∃ source ∈ P.sourceImages a F, ∃ U : Set Space, IsOpen U ∧ (b : Space) ∈ U ∧
      ∀ x ∈ U ∩ frontier P.body, P.surfaceDist a x = dist source (P.faceCoordinates F x) := by
  obtain ⟨f, hf⟩ := P.geodesicFiber_nonempty a b
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  obtain ⟨source, member, _, W, openW, fW, formula⟩ := small_geodesic_branch_distance size small_faces f hf.1
    (by simpa only [first, last] using different) F (by simpa only [last] using unique_face)
  obtain ⟨N, openN, abN, contains⟩ := P.geodesic_family_upper_continuous (a, b) W openW
    (fun g geodesic ends => unique_route ⟨geodesic, ends⟩ hf ▸ fW)
  let V : Set (frontier P.body) := (fun c => (a, c)) ⁻¹' N
  have openV : IsOpen V := openN.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨U, openU, sameU⟩ := isOpen_induced_iff.mp openV
  refine ⟨source, by simpa only [first] using member, U, openU, ?_, ?_⟩
  · have bV : b ∈ V := abN
    rw [← sameU] at bV
    exact bV
  · intro x hx
    let c : frontier P.body := ⟨x, hx.2⟩
    have cV : c ∈ V := sameU ▸ hx.1
    obtain ⟨g, hg⟩ := P.geodesicFiber_nonempty a c
    have gW := contains g hg.1 (hg.2 ▸ cV)
    have result := formula g gW hg.1 ((congrArg Prod.fst hg.2).trans first.symm)
    have g0 : g 0 = a := congrArg Prod.fst hg.2
    have g1 : g 1 = c := congrArg Prod.snd hg.2
    simpa only [g0, g1] using result

end SixVertexUnfolding.ConvexPolyhedron
