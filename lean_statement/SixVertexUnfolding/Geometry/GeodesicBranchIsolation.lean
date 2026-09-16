import SixVertexUnfolding.Geometry.GeodesicCurveNonbranching
import SixVertexUnfolding.Geometry.UniqueFaceNeighborhoods
import SixVertexUnfolding.Geometry.ShortestTerminalCoordinates

/-! Near a route ending inside one face, its source copy cannot change.
Consequently nearby routes with the same endpoints coincide. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set BoundedContinuousFunction

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- For a fixed source, the endpoint map is locally injective around each route ending in a unique face. -/
theorem geodesic_branch_isolation (f : P.BoundaryCurve) (different : f 0 ≠ f 1)
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
    simpa only [source_g] using graph.recoveredSource_mem small_faces g geodesic_g gW.2.2.1 F g_unique t before g_inside
  have h_member : P.recoveredSource F t h ∈ P.sourceImages (f 0) F := by
    simpa only [source_h] using graph.recoveredSource_mem small_faces h geodesic_h hW.2.2.1 F h_unique t before h_inside
  have same_source := (isolated g gW.2.2.2 g_member).trans (isolated h hW.2.2.2 h_member).symm
  have same_position := P.recoveredSource_position F t before g h same_source target
  have meet : g t = h t := by
    apply Subtype.ext
    apply dist_eq_zero.mp
    rw [← P.faceCoordinates_rigid F _ g_inside _ h_inside, same_position, dist_self]
  exact graph.geodesic_curves_agree_of_meeting small_faces g h geodesic_g geodesic_h gW.2.2.1
    (source_g.trans source_h.symm) target t positive before meet

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
