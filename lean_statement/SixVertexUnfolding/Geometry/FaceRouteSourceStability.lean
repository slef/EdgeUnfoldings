import SixVertexUnfolding.Geometry.UniqueRouteSourceDistance

/-! Continuous route families retain their actual terminal source copy
while their targets stay inside a fixed original face. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set BoundedContinuousFunction

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Near a route ending inside one face, its actual terminal source copy is fixed. -/
theorem geodesic_branch_terminal_source (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (F : P.Face) (unique : ∀ G : P.Face, (f 1 : Space) ∈ G.val → G = F) :
    ∃ source ∈ P.sourceImages (f 0) F, P.HasTerminalSource f F source ∧
      ∃ W : Set P.BoundaryCurve, IsOpen W ∧ f ∈ W ∧
      ∀ g ∈ W, g ∈ P.geodesicCurves → g 0 = f 0 → P.HasTerminalSource g F source := by
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
  obtain ⟨source, source_mem, terminal⟩ := graph.exists_terminal_source small_faces f geodesic different F unique
  have original := terminal.recovered_eq geodesic t before (covers _ ⟨ftU, (f t).property⟩).1
  refine ⟨source, source_mem, terminal, W, openW, ⟨ftU, targetU, different, fV⟩, ?_⟩
  intro g near shortest same_start
  have inside := (covers _ ⟨near.1, (g t).property⟩).1
  have target := covers _ ⟨near.2.1, (g 1).property⟩
  obtain ⟨other, _, terminal_g⟩ := graph.exists_terminal_source small_faces g shortest near.2.2.1 F target.2
  have recovered := terminal_g.recovered_eq shortest t before inside
  have member : P.recoveredSource F t g ∈ P.sourceImages (f 0) F := by
    simpa only [same_start] using graph.recoveredSource_mem small_faces g shortest near.2.2.1 F target.2 t before inside
  have same : other = source := recovered.symm.trans ((isolated g near.2.2.2 member).trans original)
  simpa only [same] using terminal_g

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
