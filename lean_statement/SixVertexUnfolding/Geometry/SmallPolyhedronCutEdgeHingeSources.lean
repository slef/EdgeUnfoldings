import SixVertexUnfolding.Geometry.CutEdgeHingeSources
import SixVertexUnfolding.Geometry.SmallPolyhedronEdgeRouteFamilySource
import SixVertexUnfolding.Geometry.SmallPolyhedronEdgeSources
import SixVertexUnfolding.Geometry.SmallPolyhedronJunctions

/-! The two fixed source copies also exist when a cut-tree edge lies
on an original hinge. One joined development covers both incident faces.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G) (size : P.vertices.card ≤ 6)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Along an original hinge, both route sides have fixed, distinct source copies. -/
theorem small_cut_edge_hinge_sources (shared : P.ShareEdge F G) (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge)
    (on_edge : ∀ t, (T.openEdgeTarget edge t : Space) ∈ F.val ∩ G.val) :
    ∃ p ∈ chart.sourceImages a, ∃ q ∈ chart.sourceImages a, p ≠ q ∧
      (∀ t, chart.HasTerminalSource (S.first t) p ∧ chart.HasTerminalSource (S.second t) q) ∧
      ∀ t : unitInterval,
        P.surfaceDist a (T.closedEdgeTarget edge t) = dist p (chart.left (T.closedEdgeTarget edge t)) ∧
        P.surfaceDist a (T.closedEdgeTarget edge t) = dist q (chart.left (T.closedEdgeTarget edge t)) := by
  letI : PreconnectedSpace (Ioo (0 : ℝ) 1) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  let middle : Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  obtain ⟨p, p_mem, first⟩ := chart.small_edge_route_family_source size small_faces shared a middle
    (T.openEdgeTarget edge) S.first S.first_member (T.openEdgeTarget_different edge)
    on_edge (T.openEdgeTarget_nonvertex edge)
  obtain ⟨q, q_mem, second⟩ := chart.small_edge_route_family_source size small_faces shared a middle
    (T.openEdgeTarget edge) S.second S.second_member (T.openEdgeTarget_different edge)
    on_edge (T.openEdgeTarget_nonvertex edge)
  have distinct : p ≠ q := by
    intro same
    have f0 : S.first middle 0 = a := congrArg Prod.fst (S.first_member middle).2
    have f1 : S.first middle 1 = T.openEdgeTarget edge middle := congrArg Prod.snd (S.first_member middle).2
    apply S.distinct middle
    exact chart.small_routes_agree_of_terminal_source size small_faces _ _ (S.first_member middle).1
      (S.second_member middle).1 (by simpa only [f0, f1] using T.openEdgeTarget_different edge middle)
      (f0.trans (congrArg Prod.fst (S.second_member middle).2).symm)
      (f1.trans (congrArg Prod.snd (S.second_member middle).2).symm) p (first middle).1
      (by simpa only [same] using (second middle).1)
  have extend_formula (s : Plane)
      (formula : ∀ t, P.surfaceDist a (T.openEdgeTarget edge t) = dist s (chart.unfold (T.openEdgeTarget edge t)))
      (t : unitInterval) :
      P.surfaceDist a (T.closedEdgeTarget edge t) = dist s (chart.left (T.closedEdgeTarget edge t)) := by
    have left_cont : Continuous (fun t => P.surfaceDist a (T.closedEdgeTarget edge t)) :=
      P.surfaceDist_continuous.comp (continuous_const.prodMk (T.closedEdgeTarget edge).continuous)
    have right_cont : Continuous (fun t => dist s (chart.left (T.closedEdgeTarget edge t))) :=
      continuous_const.dist (chart.left.continuous_of_finiteDimensional.comp
        (continuous_subtype_val.comp (T.closedEdgeTarget edge).continuous))
    have equal := Continuous.ext_on interiorTime_dense left_cont right_cont (by
      rintro _ ⟨x, rfl⟩
      simpa only [chart.unfold_of_first (on_edge x).1] using formula x)
    exact congrFun equal t
  exact ⟨p, p_mem, q, q_mem, distinct, fun t => ⟨(first t).1, (second t).1⟩,
    fun t => ⟨extend_formula p (fun x => (first x).2) t, extend_formula q (fun x => (second x).2) t⟩⟩

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
