import SixVertexUnfolding.Geometry.StarFlatDiskMetric
import SixVertexUnfolding.Geometry.SmallPolyhedronStarInverseDisks
import SixVertexUnfolding.Geometry.SmallPolyhedronStarInversePatchMetric

/-! On a sufficiently small actual flat disk, the assembled development
preserves every pairwise distance. Both inequalities are proved.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

theorem small_develop_isometric_on_small_flat_disk {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (separated : charts.KitesSeparated)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (b : P.UncutSurface a) (flat : P.FlatChart (b.val : Space)) :
    ∃ ε > 0, ∃ _contained : Metric.ball flat.origin ε ⊆ flat.domain,
      ∃ inclusion : C(Metric.ball flat.origin ε, P.UncutSurface a),
        (∀ x, ((inclusion x).val : Space) = flat.map x) ∧
        Isometry (fun x => charts.develop (inclusion x).val) := by
  obtain ⟨radius, rp, inverse, pieces, _, recovers⟩ :=
    small_every_retained_point_has_inverse_disk size small_faces charts separated cofacial b
  obtain ⟨δ, dp, domain, uncut⟩ := flat.exists_uncut_disk a b.val rfl b.property
  let ε := min δ (radius / 2)
  have ep : 0 < ε := lt_min dp (half_pos rp)
  have contained : Metric.ball flat.origin ε ⊆ flat.domain := fun x hx =>
    domain ((Metric.mem_ball.mp hx).trans_le (min_le_left _ _))
  have retained (x : Metric.ball flat.origin ε) :
      (⟨flat.map x, flat.on_surface (contained x.property)⟩ : frontier P.body) ∉ P.starCuts a :=
    uncut ⟨x, (Metric.mem_ball.mp x.property).trans_le (min_le_left _ _)⟩
  let inclusion : C(Metric.ball flat.origin ε, P.UncutSurface a) :=
    ⟨fun x => ⟨⟨flat.map x, flat.on_surface (contained x.property)⟩, retained x⟩,
      ((flat.continuous.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩
  let center : Metric.ball flat.origin ε := ⟨flat.origin, Metric.mem_ball_self ep⟩
  have at_center : inclusion center = b := by
    apply Subtype.ext
    exact Subtype.ext flat.at_origin
  have forward := small_develop_flat_patch_nonexpanding size small_faces charts cofacial flat
    (Metric.ball flat.origin ε) (convex_ball _ _) contained inclusion (fun _ => rfl)
  have developed_inside (x : Metric.ball flat.origin ε) :
      charts.develop (inclusion x).val ∈ Metric.ball (charts.develop b.val) radius := by
    have bound := forward.dist_le_mul x center
    rw [at_center] at bound
    have small : dist (x : Plane) flat.origin < radius :=
      (Metric.mem_ball.mp x.property).trans_le ((min_le_right _ _).trans (by linarith))
    exact lt_of_le_of_lt (by simpa only [NNReal.coe_one, one_mul] using bound) small
  let fold : C(Metric.ball (charts.develop b.val) radius, frontier P.body) :=
    ⟨fun x => (inverse x).val, continuous_subtype_val.comp inverse.continuous⟩
  refine ⟨ε, ep, contained, inclusion, fun _ => rfl, ?_⟩
  apply small_develop_flat_patch_isometric_of_folding size small_faces charts cofacial flat
    (Metric.ball flat.origin ε) (convex_ball _ _) contained inclusion (fun _ => rfl)
    _ fold pieces developed_inside
  · intro x
    exact congrArg Subtype.val (recovers (inclusion x) (developed_inside x))
  · intro x y
    exact (convex_ball _ _).segment_subset (developed_inside x) (developed_inside y)

end SixVertexUnfolding.ConvexPolyhedron
