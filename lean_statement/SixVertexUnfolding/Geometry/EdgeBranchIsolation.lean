import SixVertexUnfolding.Geometry.EdgeSourceStability
import SixVertexUnfolding.Geometry.GeodesicBranchIsolation

/-! Nearby routes with the same endpoints cannot split at an original edge.
Combined with the face result, this applies at every nonvertex target. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set BoundedContinuousFunction

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Local injectivity of the target map also holds when the old target lies inside an original edge. -/
theorem geodesic_branch_isolation_at_edge (f : P.BoundaryCurve) (different : f 0 ≠ f 1)
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
    simpa only [first_g] using chart.recoveredSource_mem graph small_faces g hg gW.2.2.1 U openU gW.2.1
      (only_two _ gW.2.1) metric t before gW.1
  have h_member : chart.recoveredSource t h ∈ chart.sourceImages (f 0) := by
    simpa only [first_h] using chart.recoveredSource_mem graph small_faces h hh hW.2.2.1 U openU hW.2.1
      (only_two _ hW.2.1) metric t before hW.1
  have same := (isolated g gW.2.2.2 g_member).trans (isolated h hW.2.2.2 h_member).symm
  have positions := chart.recoveredSource_position t before g h same last
  have meet : g t = h t := by
    apply Subtype.ext
    have equal := congrArg chart.fold.map positions
    rwa [chart.fold_unfold (covers ⟨gW.1, (g t).property⟩), chart.fold_unfold (covers ⟨hW.1, (h t).property⟩)] at equal
  exact graph.geodesic_curves_agree_of_meeting small_faces g h hg hh gW.2.2.1
    (first_g.trans first_h.symm) last t positive before meet

include graph small_faces in
/-- Route branches cannot split near any nonvertex target, including original edge interiors. -/
theorem geodesic_branch_isolation_nonvertex (f : P.BoundaryCurve) (different : f 0 ≠ f 1)
    (not_vertex : (f 1 : Space) ∉ P.vertices) :
    ∃ W : Set P.BoundaryCurve, IsOpen W ∧ f ∈ W ∧
      ∀ g ∈ W, ∀ h ∈ W, g ∈ P.geodesicCurves → h ∈ P.geodesicCurves →
        g 0 = f 0 → h 0 = f 0 → g 1 = h 1 → g = h := by
  rcases P.nonvertex_incident_facets (f 1).property not_vertex with ⟨F, _, unique⟩ | ⟨F, G, shared, target, _⟩
  · exact graph.geodesic_branch_isolation small_faces f different F unique
  · exact graph.geodesic_branch_isolation_at_edge small_faces f different F G shared target not_vertex

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
