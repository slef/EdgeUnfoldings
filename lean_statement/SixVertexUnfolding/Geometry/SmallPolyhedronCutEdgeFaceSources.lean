import SixVertexUnfolding.Geometry.CutEdgeFaceSources
import SixVertexUnfolding.Geometry.SmallPolyhedronEdgeSources
import SixVertexUnfolding.Geometry.SmallPolyhedronFaceRouteFamilySource
import SixVertexUnfolding.Geometry.SmallPolyhedronJunctions

/-! A cut-tree edge inside an original face has two fixed, distinct
planar source copies. Their distances give the source distance along
the entire closed edge, including its tree vertices.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- The two source copies for an edge inside a face are constant and distinct. -/
theorem small_cut_edge_face_sources (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) (F : P.Face)
    (unique_face : ∀ t, ∀ G : P.Face, (T.openEdgeTarget edge t : Space) ∈ G.val → G = F) :
    ∃ p ∈ P.sourceImages a F, ∃ q ∈ P.sourceImages a F, p ≠ q ∧
      (∀ t, P.HasTerminalSource (S.first t) F p ∧ P.HasTerminalSource (S.second t) F q) ∧
      ∀ t : unitInterval,
        P.surfaceDist a (T.closedEdgeTarget edge t) = dist p (P.faceCoordinates F (T.closedEdgeTarget edge t)) ∧
        P.surfaceDist a (T.closedEdgeTarget edge t) = dist q (P.faceCoordinates F (T.closedEdgeTarget edge t)) := by
  letI : PreconnectedSpace (Ioo (0 : ℝ) 1) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  let middle : Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  obtain ⟨p, p_mem, first⟩ := small_face_route_family_source size small_faces a middle
    (T.openEdgeTarget edge) S.first S.first_member (T.openEdgeTarget_different edge) F unique_face
  obtain ⟨q, q_mem, second⟩ := small_face_route_family_source size small_faces a middle
    (T.openEdgeTarget edge) S.second S.second_member (T.openEdgeTarget_different edge) F unique_face
  have distinct : p ≠ q := by
    intro same
    have f0 : S.first middle 0 = a := congrArg Prod.fst (S.first_member middle).2
    have f1 : S.first middle 1 = T.openEdgeTarget edge middle := congrArg Prod.snd (S.first_member middle).2
    apply S.distinct middle
    exact small_routes_agree_of_terminal_source size small_faces _ _ (S.first_member middle).1
      (S.second_member middle).1 (by simpa only [f0, f1] using T.openEdgeTarget_different edge middle)
      (f0.trans (congrArg Prod.fst (S.second_member middle).2).symm)
      (f1.trans (congrArg Prod.snd (S.second_member middle).2).symm) F p (first middle).1
      (by simpa only [same] using (second middle).1)
  have extend_formula (s : Plane)
      (formula : ∀ t, P.surfaceDist a (T.openEdgeTarget edge t) =
        dist s (P.faceCoordinates F (T.openEdgeTarget edge t))) (t : unitInterval) :
      P.surfaceDist a (T.closedEdgeTarget edge t) = dist s (P.faceCoordinates F (T.closedEdgeTarget edge t)) := by
    have left_cont : Continuous (fun t => P.surfaceDist a (T.closedEdgeTarget edge t)) :=
      P.surfaceDist_continuous.comp (continuous_const.prodMk (T.closedEdgeTarget edge).continuous)
    have right_cont : Continuous (fun t => dist s (P.faceCoordinates F (T.closedEdgeTarget edge t))) :=
      continuous_const.dist ((P.faceCoordinates F).continuous_of_finiteDimensional.comp
        (continuous_subtype_val.comp (T.closedEdgeTarget edge).continuous))
    have equal := Continuous.ext_on interiorTime_dense left_cont right_cont (by
      rintro _ ⟨x, rfl⟩
      exact formula x)
    exact congrFun equal t
  exact ⟨p, p_mem, q, q_mem, distinct, fun t => ⟨(first t).1, (second t).1⟩,
    fun t => ⟨extend_formula p (fun x => (first x).2) t, extend_formula q (fun x => (second x).2) t⟩⟩

end SixVertexUnfolding.ConvexPolyhedron
