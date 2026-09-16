import SixVertexUnfolding.Geometry.RouteBranchSeparation
import SixVertexUnfolding.Geometry.SmallPolyhedronEdgeSources
import SixVertexUnfolding.Geometry.SmallPolyhedronFaceRouteSourceStability
import SixVertexUnfolding.Geometry.SmallPolyhedronJunctions

/-! Distinct continuous shortest-route branches cannot merge at a
nonsource nonvertex target. Local terminal-source stability prevents it.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Near one route ending at a nonvertex, there is at most one shortest
route for each target and the same source. -/
theorem small_geodesic_branch_locally_unique (f : P.BoundaryCurve)
    (geodesic : f ∈ P.geodesicCurves) (different : f 0 ≠ f 1)
    (not_vertex : (f 1 : Space) ∉ P.vertices) :
    ∃ W : Set P.BoundaryCurve, IsOpen W ∧ f ∈ W ∧
      ∀ g ∈ W, ∀ h ∈ W, g ∈ P.geodesicCurves → h ∈ P.geodesicCurves →
        g 0 = f 0 → h 0 = f 0 → g 1 = h 1 → g = h := by
  have open_distinct : IsOpen {g : P.BoundaryCurve | g 0 ≠ g 1} :=
    (isClosed_eq (continuous_eval_const 0) (continuous_eval_const 1)).isOpen_compl
  rcases P.nonvertex_incident_facets (f 1).property not_vertex with
    ⟨F, _, unique⟩ | ⟨F, G, shared, target, _⟩
  · obtain ⟨p, _, _, W, openW, fW, terminal⟩ :=
      small_geodesic_branch_terminal_source size small_faces f geodesic different F unique
    refine ⟨W ∩ {g | g 0 ≠ g 1}, openW.inter open_distinct, ⟨fW, different⟩, ?_⟩
    intro g hg h hh gg hh_geo gs hs ends
    exact small_routes_agree_of_terminal_source size small_faces g h gg hh_geo hg.2
      (gs.trans hs.symm) ends F p (terminal g hg.1 gg gs) (terminal h hh.1 hh_geo hs)
  · obtain ⟨center, inside⟩ := P.solid
    obtain ⟨facets⟩ := P.exists_normalized_facets inside
    obtain ⟨chart⟩ := exists_edge_folding facets F G shared
    obtain ⟨patch⟩ := chart.exists_metric_patch shared target not_vertex
    obtain ⟨p, _, _, W, openW, fW, terminal⟩ :=
      patch.small_geodesic_branch_source size small_faces f geodesic different patch.center_mem
    refine ⟨W ∩ {g | g 0 ≠ g 1}, openW.inter open_distinct, ⟨fW, different⟩, ?_⟩
    intro g hg h hh gg hh_geo gs hs ends
    exact chart.small_routes_agree_of_terminal_source size small_faces g h gg hh_geo hg.2
      (gs.trans hs.symm) ends p (terminal g hg.1 gg gs).1 (terminal h hh.1 hh_geo hs).1

include size small_faces in
/-- If two continuous branches are distinct at every positive interior
parameter, their limits at a nonvertex endpoint are distinct as well. -/
theorem small_route_branches_distinct_at_zero (a : frontier P.body)
    (target : C(unitInterval, frontier P.body))
    (first second : C(unitInterval, P.BoundaryCurve))
    (first_member : ∀ t, first t ∈ P.geodesicFiber a (target t))
    (second_member : ∀ t, second t ∈ P.geodesicFiber a (target t))
    (different : a ≠ target 0) (not_vertex : (target 0 : Space) ∉ P.vertices)
    (distinct : ∀ t : unitInterval, 0 < t → t < 1 → first t ≠ second t) :
    first 0 ≠ second 0 := by
  intro same
  have starts (t : unitInterval) : first t 0 = a := congrArg Prod.fst (first_member t).2
  have ends (t : unitInterval) : first t 1 = target t := congrArg Prod.snd (first_member t).2
  obtain ⟨W, openW, original, unique⟩ := small_geodesic_branch_locally_unique size small_faces
    (first 0) (first_member 0).1 (by simpa only [starts, ends] using different)
    (by simpa only [ends] using not_vertex)
  have other : second 0 ∈ W := same ▸ original
  obtain ⟨ε, positive, near⟩ := Metric.isOpen_iff.mp
    ((openW.preimage first.continuous).inter (openW.preimage second.continuous))
    (0 : unitInterval) ⟨original, other⟩
  obtain ⟨s, sp, short⟩ := exists_between (lt_min positive (show (0 : ℝ) < 1 by norm_num))
  let t : unitInterval := ⟨s, sp.le, (short.trans_le (min_le_right _ _)).le⟩
  have member : t ∈ Metric.ball (0 : unitInterval) ε := by
    change dist s (0 : ℝ) < ε
    simpa only [Real.dist_eq, sub_zero, abs_of_pos sp] using short.trans_le (min_le_left _ _)
  have close := near member
  apply distinct t sp (short.trans_le (min_le_right _ _))
  apply unique (first t) close.1 (second t) close.2 (first_member t).1 (second_member t).1
  · exact (starts t).trans (starts 0).symm
  · exact (congrArg Prod.fst (second_member t).2).trans (starts 0).symm
  · exact (ends t).trans (congrArg Prod.snd (second_member t).2).symm

end SixVertexUnfolding.ConvexPolyhedron
