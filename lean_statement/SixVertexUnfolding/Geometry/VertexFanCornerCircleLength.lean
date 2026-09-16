import SixVertexUnfolding.Geometry.VertexFanCircleDistances
import SixVertexUnfolding.Geometry.TriangleCornerArcs
import SixVertexUnfolding.Geometry.RadialStripCornerGeometry
import SixVertexUnfolding.Geometry.ClosedCoverDistance

/-! A small circular corner arc of an actual radial triangle folds to
a nonexpanding arc of the original vertex's angular circle. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan

open Set EuclideanGeometry

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  (fan : P.VertexFaceFan pole n)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- One radius bound gives a circle arc of at most the triangle corner angle.
All points on that circular section are included in its image. -/
theorem folded_corner_circle_arc {routes : C(unitInterval, P.BoundaryCurve)} {p l r : Plane}
    (D : RadialStripTriangle routes p l r) (noncollinear : ¬ Collinear ℝ ({p, l, r} : Set Plane))
    (corner : convexHull ℝ ({p, l, r} : Set Plane)) (at_l : (corner : Plane) = l)
    (at_pole : ((D.homeomorph.symm corner).val : Space) = pole) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε,
      ∃ f : ℝ → AddCircle (fan.totalAngle),
        (∀ s ∈ Icc (0 : ℝ) (angle p l r), ∀ t ∈ Icc (0 : ℝ) (angle p l r),
          dist (f s) (f t) ≤ dist s t) ∧
        ∀ z : convexHull ℝ ({p, l, r} : Set Plane), dist (z : Plane) l = ρ →
          fan.fanCircleMap ((D.homeomorph.symm z).val : Space) ∈ f '' Icc (0 : ℝ) (angle p l r) := by
  obtain ⟨ε, ep, arcs⟩ := exists_triangle_corner_arcs p l r noncollinear
  obtain ⟨δ, dp, radial⟩ := D.local_radial_distance corner
  obtain ⟨U, openU, poleU, fan_cover⟩ := fan.surface_neighborhood small_faces
  obtain ⟨R, Rp, ballU⟩ := Metric.isOpen_iff.mp openU (pole) poleU
  refine ⟨min ε (min δ R), lt_min ep (lt_min dp Rp), ?_⟩
  intro ρ hr
  have smallε : ρ < ε := hr.2.trans_le (min_le_left _ _)
  have smallδ : ρ < δ := hr.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have smallR : ρ < R := hr.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨arc⟩ := arcs ρ ⟨hr.1, smallε⟩
  let folded (θ : ℝ) : Space := ((D.homeomorph.symm (arc.point θ)).val : Space)
  have continuous_folded : Continuous folded := continuous_subtype_val.comp
    (continuous_subtype_val.comp (D.homeomorph.symm.continuous.comp arc.point.continuous))
  have radius (θ : ℝ) : dist (folded θ) (pole) = ρ := by
    have near : dist (arc.point θ : Plane) corner < δ := by rw [at_l, arc.radius]; exact smallδ
    have equal := radial (arc.point θ) near
    rw [at_pole, at_l, arc.radius] at equal
    exact equal
  have nonpole (θ : ℝ) : folded θ ≠ pole := by
    intro equal
    have contradiction := radius θ
    rw [equal, dist_self] at contradiction
    exact (ne_of_gt hr.1) contradiction.symm
  have located (θ : ℝ) : folded θ ∈ fan.fanCircleDomain := by
    refine ⟨fan_cover ⟨ballU ?_, ?_⟩, nonpole θ⟩
    · rw [Metric.mem_ball, radius]
      exact smallR
    · exact (D.homeomorph.symm (arc.point θ)).val.property
  let f : ℝ → AddCircle (fan.totalAngle) := fun θ => fan.fanCircleMap (folded θ)
  have continuous_f : Continuous f :=
    (fan.fanCircleMap_continuousOn small_faces).comp_continuous continuous_folded located
  let pieces (i : Fin n) : Set ℝ := folded ⁻¹' fan.triangle i
  have closed (i : Fin n) : IsClosed (pieces i) :=
    (fan.triangle_isCompact _).isClosed.preimage continuous_folded
  have covers : Icc (0 : ℝ) (angle p l r) ⊆ ⋃ i, pieces i := by
    intro θ _
    obtain ⟨i, hi⟩ := mem_iUnion.mp (located θ).1
    exact mem_iUnion.mpr ⟨i, hi⟩
  refine ⟨f, interval_nonexpanding_of_closed_cover f 0 (angle p l r)
    continuous_f.continuousOn pieces closed covers ?_, ?_⟩
  · intro i s hs t ht
    have spatial := fan.fanCircleMap_dist_le_angle small_faces i (folded s) (folded t)
      hs.2 ht.2 (nonpole s) (nonpole t)
    have planar := triangle_angle_le_of_distances (pole) (folded s) (folded t)
      l (arc.point s) (arc.point t)
      (by rw [dist_comm l, arc.radius, dist_comm (pole : Space), radius])
      (by rw [dist_comm l, arc.radius, dist_comm (pole : Space), radius])
      (by simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using
        D.inverse_nonexpanding.dist_le_mul (arc.point s) (arc.point t))
    exact spatial.trans (planar.trans (arc.angle_bound s hs.1 t ht.1))
  · intro z hz
    obtain ⟨θ, hθ, same⟩ := arc.covers z hz
    refine ⟨θ, hθ, ?_⟩
    change fan.fanCircleMap ((D.homeomorph.symm (arc.point θ)).val : Space) = _
    rw [same]

end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan
