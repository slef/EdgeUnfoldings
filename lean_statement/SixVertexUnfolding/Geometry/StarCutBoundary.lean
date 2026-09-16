import SixVertexUnfolding.Geometry.StarPolygonClosure
import SixVertexUnfolding.Geometry.StarOpenEmbedding
import SixVertexUnfolding.Geometry.RegularPatchAgreement

/-! A triangle representation lies in the open developed surface exactly
when its actual surface point is uncut. Continuity of the true inverse
excludes cut-ray copies from the planar interior. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

/-- Every represented point of a closed triangle is in the star image precisely when it is uncut. -/
theorem triangle_point_in_range_iff_uncut {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v : T.vertices} (edge : T.graph.Adj u v) (side : Bool)
    (b : frontier P.body) (inside : b ∈ range (closedRouteStripMap ((charts.global edge).routes side))) :
    (((charts.global edge).sideTriangle side).homeomorph ⟨b, inside⟩ : Plane) ∈
        range (fun c : P.UncutSurface a => charts.develop c.val) ↔ b ∉ P.starCuts a := by
  let D := charts.global edge
  let q := (D.sideTriangle side).homeomorph ⟨b, inside⟩
  let fold : C(D.sideRegion side, frontier P.body) :=
    ⟨fun x => ((D.sideTriangle side).homeomorph.symm x).val,
      continuous_subtype_val.comp (D.sideTriangle side).homeomorph.symm.continuous⟩
  constructor
  · rintro ⟨c, at_q⟩
    change charts.develop c.val = (q : Plane) at at_q
    obtain ⟨radius, positive, inverse, _, _, left_inverse⟩ :=
      graph.every_retained_point_has_inverse_disk small_faces charts source at_source cofacial c
    let U := Metric.ball (charts.develop c.val) radius
    let inverse_surface : C(U, frontier P.body) :=
      ⟨fun x => (inverse x).val, continuous_subtype_val.comp inverse.continuous⟩
    have agreement : ∀ x : D.sideRegion side, (x : Plane) ∈ interior (D.sideRegion side) →
        ∀ member : (x : Plane) ∈ U, fold x = inverse_surface ⟨x, member⟩ := by
      intro x interior_x member
      let y := (D.sideTriangle side).homeomorph.symm x
      have at_x : ((D.sideTriangle side).homeomorph y : Plane) = x :=
        congrArg Subtype.val ((D.sideTriangle side).homeomorph.apply_symm_apply x)
      have outside := graph.placed_triangle_interior_uncut small_faces D cofacial side y.val y.property
        (at_x.symm ▸ interior_x)
      let retained : P.UncutSurface a := ⟨y.val, outside⟩
      have developed : charts.develop retained.val = (x : Plane) :=
        graph.develop_agrees small_faces charts cofacial edge outside ⟨side, y.property, at_x⟩
      have returns := left_inverse retained (by rw [developed]; exact member)
      have same : inverse ⟨x, member⟩ = retained := by simpa only [developed] using returns
      exact (congrArg Subtype.val same).symm
    have q_in : (q : Plane) ∈ U := by
      change dist (q : Plane) (charts.develop c.val) < radius
      rw [at_q]
      simpa only [dist_self] using positive
    have at_boundary := regular_patch_agreement (D.sideRegion side) (D.side_regular side)
      fold U Metric.isOpen_ball inverse_surface agreement q q_in
    have returns : fold q = b := congrArg Subtype.val ((D.sideTriangle side).homeomorph.symm_apply_apply ⟨b, inside⟩)
    rw [returns] at at_boundary
    exact at_boundary.symm ▸ (inverse ⟨q, q_in⟩).property
  · intro outside
    exact ⟨⟨b, outside⟩, graph.develop_on_triangle small_faces charts cofacial edge side b inside outside⟩

/-- The boundary copies in every actual triangle are exactly copies of removed star-cut points. -/
theorem triangle_point_boundary_iff_cut {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v : T.vertices} (edge : T.graph.Adj u v) (side : Bool)
    (b : frontier P.body) (inside : b ∈ range (closedRouteStripMap ((charts.global edge).routes side))) :
    (((charts.global edge).sideTriangle side).homeomorph ⟨b, inside⟩ : Plane) ∈
        frontier (range (fun c : P.UncutSurface a => charts.develop c.val)) ↔ b ∈ P.starCuts a := by
  have closure_member : (((charts.global edge).sideTriangle side).homeomorph ⟨b, inside⟩ : Plane) ∈
      closure (range (fun c : P.UncutSurface a => charts.develop c.val)) := by
    rw [graph.closure_develop_range_eq_closedImage small_faces charts cofacial]
    exact mem_iUnion.mpr ⟨(⟨(u, v), edge⟩ : T.graph.Dart),
      (charts.global edge).side_subset_kite side
        (((charts.global edge).sideTriangle side).homeomorph ⟨b, inside⟩).property⟩
  have open_range := (graph.develop_isOpenEmbedding small_faces charts source at_source cofacial).isOpen_range
  rw [frontier, open_range.interior_eq]
  simp only [mem_diff, closure_member, true_and,
    graph.triangle_point_in_range_iff_uncut small_faces charts source at_source cofacial edge side b inside,
    not_not]

/-- Every global triangle placement respects precisely the intended cut boundary. -/
theorem placement_boundary_iff_cut {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v : T.vertices} (edge : T.graph.Adj u v) {b : frontier P.body} {x : Plane}
    (placed : (charts.global edge).Places b x) :
    x ∈ frontier (range (fun c : P.UncutSurface a => charts.develop c.val)) ↔ b ∈ P.starCuts a := by
  obtain ⟨side, inside, value⟩ := placed
  rw [← value]
  exact graph.triangle_point_boundary_iff_cut small_faces charts source at_source cofacial edge side b inside

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
