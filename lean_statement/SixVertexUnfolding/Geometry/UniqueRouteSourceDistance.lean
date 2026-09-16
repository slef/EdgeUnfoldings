import SixVertexUnfolding.Geometry.TerminalSourceData
import SixVertexUnfolding.Geometry.UniqueGeodesicNeighborhoods

/-! At a target with a unique route, intrinsic distance is locally one
fixed source-distance formula, even when unused candidate copies have ties. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set BoundedContinuousFunction

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Around one route, every nearby route from the same source uses its fixed planar distance formula. -/
theorem geodesic_branch_distance (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
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
  obtain ⟨actual, _, terminal⟩ := graph.exists_terminal_source small_faces f geodesic different F unique
  have same := terminal.recovered_eq geodesic t before (covers _ ⟨ftU, (f t).property⟩).1
  have recovered_terminal : P.HasTerminalSource f F (P.recoveredSource F t f) := by rw [same]; exact terminal
  refine ⟨P.recoveredSource F t f, graph.recoveredSource_mem small_faces f geodesic different F unique t before
    (covers _ ⟨ftU, (f t).property⟩).1, recovered_terminal, W, openW, ⟨ftU, targetU, different, fV⟩, ?_⟩
  intro g near shortest same_start
  have inside := (covers _ ⟨near.1, (g t).property⟩).1
  have target := covers _ ⟨near.2.1, (g 1).property⟩
  have member : P.recoveredSource F t g ∈ P.sourceImages (f 0) F := by
    simpa only [same_start] using graph.recoveredSource_mem small_faces g shortest near.2.2.1 F target.2 t before inside
  rw [P.recoveredSource_distance g shortest F t before inside target.1, isolated g near.2.2.2 member]

include graph small_faces in
/-- Actual route uniqueness suffices for a local source-distance formula; candidate-distance ties are allowed. -/
theorem unique_route_source_distance (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F)
    (unique_route : (P.geodesicFiber a b).Subsingleton) :
    ∃ source ∈ P.sourceImages a F, ∃ U : Set Space, IsOpen U ∧ (b : Space) ∈ U ∧
      ∀ x ∈ U ∩ frontier P.body, P.surfaceDist a x = dist source (P.faceCoordinates F x) := by
  obtain ⟨f, hf⟩ := P.geodesicFiber_nonempty a b
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  obtain ⟨source, member, _, W, openW, fW, formula⟩ := graph.geodesic_branch_distance small_faces f hf.1
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

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
