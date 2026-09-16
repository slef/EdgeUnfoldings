import SixVertexUnfolding.Geometry.StarOpenEmbedding
import SixVertexUnfolding.Geometry.SmallPolyhedronStarInverseDisks

/-! The assembled cofacial-source development is globally injective
and identifies the retained surface with an open subset of the plane.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter Topology

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

/-- No two retained surface points are identified anywhere in the development. -/
theorem small_develop_injective {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (separated : charts.KitesSeparated)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    Function.Injective (fun b : P.UncutSurface a => charts.develop b.val) := by
  intro b c same
  change charts.develop b.val = charts.develop c.val at same
  obtain ⟨radius, positive, inverse, _, _, left_inverse⟩ :=
    small_every_retained_point_has_inverse_disk size small_faces charts separated cofacial b
  have b_in : charts.develop b.val ∈ Metric.ball (charts.develop b.val) radius := Metric.mem_ball_self positive
  have c_in : charts.develop c.val ∈ Metric.ball (charts.develop b.val) radius := by rw [← same]; exact b_in
  calc
    b = inverse ⟨charts.develop b.val, b_in⟩ := (left_inverse b b_in).symm
    _ = inverse ⟨charts.develop c.val, c_in⟩ := congrArg inverse (Subtype.ext same)
    _ = c := left_inverse c c_in

/-- Open retained surface regions develop to open planar regions. -/
theorem small_develop_isOpenMap {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (separated : charts.KitesSeparated)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    IsOpenMap (fun b : P.UncutSurface a => charts.develop b.val) := by
  intro S openS
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨b, b_in, rfl⟩
  obtain ⟨radius, positive, inverse, _, right_inverse, left_inverse⟩ :=
    small_every_retained_point_has_inverse_disk size small_faces charts separated cofacial b
  let region : Set Plane := Subtype.val '' (inverse ⁻¹' S)
  have open_region : IsOpen region := Metric.isOpen_ball.isOpenMap_subtype_val _
    (openS.preimage inverse.continuous)
  have center_in : charts.develop b.val ∈ region := by
    refine ⟨⟨charts.develop b.val, Metric.mem_ball_self positive⟩, ?_, rfl⟩
    change inverse ⟨charts.develop b.val, Metric.mem_ball_self positive⟩ ∈ S
    rw [left_inverse]
    exact b_in
  have covered : region ⊆ (fun c : P.UncutSurface a => charts.develop c.val) '' S := by
    rintro x ⟨z, member, rfl⟩
    exact ⟨inverse z, member, right_inverse z⟩
  exact mem_of_superset (open_region.mem_nhds center_in) covered

/-- The constructed development is an open embedding of the entire retained surface. -/
theorem small_develop_isOpenEmbedding {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (separated : charts.KitesSeparated)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    Topology.IsOpenEmbedding (fun b : P.UncutSurface a => charts.develop b.val) :=
  .of_continuous_injective_isOpenMap (small_develop_continuous size small_faces charts cofacial)
    (small_develop_injective size small_faces charts separated cofacial)
    (small_develop_isOpenMap size small_faces charts separated cofacial)

end SixVertexUnfolding.ConvexPolyhedron
