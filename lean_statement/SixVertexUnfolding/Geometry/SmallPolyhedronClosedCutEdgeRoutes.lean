import SixVertexUnfolding.Geometry.ClosedCutEdgeRoutes
import SixVertexUnfolding.Geometry.SmallPolyhedronShortestRoutes

/-! Every continuous shortest-route branch over an open cut-tree edge
has a continuous extension to its two tree vertices.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- An actual route family reaches definite limiting routes at both tree vertices. -/
theorem small_cut_edge_route_extension (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v)
    (routes : C(Ioo (0 : ℝ) 1, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.openEdgeTarget edge t)) :
    ∃ closed_routes : C(unitInterval, P.BoundaryCurve),
      (∀ t, closed_routes (interiorTime t) = routes t) ∧
      ∀ t, closed_routes t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t) := by
  let line : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap (u : Space) (v : Space)
  let ends : C(ℝ, Space × Space) :=
    ⟨fun t => ((a : Space), line t), continuous_const.prodMk line.continuous_of_finiteDimensional⟩
  have over_target (t : Ioo (0 : ℝ) 1) : P.spatialEndpoints (routes t) = ends t := by
    have hf := member t
    exact Prod.ext (congrArg Subtype.val (congrArg Prod.fst hf.2))
      (congrArg Subtype.val (congrArg Prod.snd hf.2))
  have left_target : ends 0 = ((a : Space), (T.vertexTarget u : Space)) := by
    apply Prod.ext
    · rfl
    · exact AffineMap.lineMap_apply_zero _ _
  have right_target : ends 1 = ((a : Space), (T.vertexTarget v : Space)) := by
    apply Prod.ext
    · rfl
    · exact AffineMap.lineMap_apply_one _ _
  have finite_left : (P.geodesicCurves ∩ P.spatialEndpoints ⁻¹' {ends 0}).Finite := by
    rw [left_target, P.spatial_geodesic_fiber]
    exact small_geodesicFiber_finite size small_faces a (T.vertexTarget u) (T.vertexTarget_different u)
  have finite_right : (P.geodesicCurves ∩ P.spatialEndpoints ⁻¹' {ends 1}).Finite := by
    rw [right_target, P.spatial_geodesic_fiber]
    exact small_geodesicFiber_finite size small_faces a (T.vertexTarget v) (T.vertexTarget_different v)
  obtain ⟨closed_routes, agrees, closed_member⟩ := finite_fiber_interval_extension routes
    P.geodesicCurves P.geodesicCurves_compact (fun t => (member t).1)
    P.spatialEndpoints P.spatialEndpoints.continuous ends over_target finite_left finite_right
  refine ⟨closed_routes, agrees, ?_⟩
  intro t
  rw [← P.spatial_geodesic_fiber]
  exact closed_member t

include size small_faces in
/-- Both sides extend together, keeping their labels and their actual shortest-route meaning. -/
theorem small_cut_edge_closed_routes (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) :
    ∃ first second : C(unitInterval, P.BoundaryCurve),
      (∀ t, first (interiorTime t) = S.first t ∧ second (interiorTime t) = S.second t) ∧
      ∀ t, first t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t) ∧
        second t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t) := by
  obtain ⟨first, first_agrees, first_member⟩ := small_cut_edge_route_extension size small_faces a T edge
    S.first S.first_member
  obtain ⟨second, second_agrees, second_member⟩ := small_cut_edge_route_extension size small_faces a T edge
    S.second S.second_member
  exact ⟨first, second, fun t => ⟨first_agrees t, second_agrees t⟩,
    fun t => ⟨first_member t, second_member t⟩⟩

end SixVertexUnfolding.ConvexPolyhedron
