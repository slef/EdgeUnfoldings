import SixVertexUnfolding.Geometry.ConnectedPlaneRigidity

/-! A planar map preserving all distances in a neighborhood of each point
is a single rigid motion on any connected open region. -/

namespace SixVertexUnfolding

open Set

/-- Local distance preservation determines one rigid motion on a connected planar region. -/
theorem connected_open_plane_local_isometry (region : Set Plane) (open_region : IsOpen region)
    (nonempty : region.Nonempty) (connected : IsPreconnected region) (f : region → Plane)
    (locally_isometric : ∀ x : region, ∃ radius > 0, ∀ y z : region,
      dist (y : Plane) x < radius → dist (z : Plane) x < radius →
      dist (f y) (f z) = dist (y : Plane) z) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, ∀ x : region, motion x = f x := by
  apply connected_plane_local_motions region nonempty connected f
  intro x
  obtain ⟨radius, positive, distances⟩ := locally_isometric x
  obtain ⟨δ, δpos, disk_in⟩ := Metric.isOpen_iff.mp open_region x x.property
  let U := Metric.ball (x : Plane) (min radius δ)
  have inside : U ⊆ region := by
    intro y hy
    exact disk_in (Metric.mem_ball.mpr
      (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_right _ _)))
  let restricted : U → Plane := fun y => f ⟨y, inside y.property⟩
  have rigid : Isometry restricted := by
    apply isometry_iff_dist_eq.mpr
    intro y z
    exact distances ⟨y, inside y.property⟩ ⟨z, inside z.property⟩
      (lt_of_lt_of_le y.property (min_le_left _ _))
      (lt_of_lt_of_le z.property (min_le_left _ _))
  have center : (x : Plane) ∈ U := Metric.mem_ball_self (lt_min positive δpos)
  obtain ⟨motion, agrees⟩ := open_planar_isometry_agrees_with_motion U Metric.isOpen_ball
    ⟨x, center⟩ restricted rigid
  exact ⟨U, Metric.isOpen_ball, center, inside, motion, agrees⟩

end SixVertexUnfolding
