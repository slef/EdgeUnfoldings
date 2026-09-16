import SixVertexUnfolding.Geometry.RadialStripLocalGeometry
import SixVertexUnfolding.Geometry.OpenPlaneRigidity

/-! Every local flat disk of a radial strip is developed by one actual
rigid planar motion, not merely a collection of distance identities. -/

namespace SixVertexUnfolding.ConvexPolyhedron.LocalFlatDisk

open Set

variable {P : ConvexPolyhedron} {region : Set (frontier P.body)} {planar : Set Plane}
  {H : region ≃ₜ planar} {b : region} (disk : LocalFlatDisk region planar H b)

/-- In each local surface coordinate disk the development is a single rigid motion. -/
theorem exists_rigid_motion : ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane,
    ∀ x : Metric.ball disk.chart.origin disk.radius, motion x = (H (disk.inclusion x) : Plane) :=
  open_planar_isometry_agrees_with_motion _ Metric.isOpen_ball
    ⟨disk.chart.origin, Metric.mem_ball_self disk.positive⟩ _ disk.isometry

/-- The local disk develops onto the complete Euclidean disk with the same radius. -/
theorem image_is_ball : range (fun x => (H (disk.inclusion x) : Plane)) = Metric.ball (H b : Plane) disk.radius := by
  obtain ⟨motion, agrees⟩ := disk.exists_rigid_motion
  have center : motion disk.chart.origin = (H b : Plane) :=
    (agrees ⟨disk.chart.origin, Metric.mem_ball_self disk.positive⟩).trans
      (congrArg (fun x => (H x : Plane)) disk.center)
  have equality : range (fun x => (H (disk.inclusion x) : Plane)) =
      motion '' Metric.ball disk.chart.origin disk.radius := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, agrees t⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, (agrees ⟨t, ht⟩).symm⟩
  rw [equality, ← center]
  exact motion.toIsometryEquiv.image_ball _ _

end SixVertexUnfolding.ConvexPolyhedron.LocalFlatDisk
