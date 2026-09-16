import SixVertexUnfolding.Geometry.GeodesicSourceRecovery
import SixVertexUnfolding.Geometry.ShortestTerminalCoordinates

/-! The recovered source gives the whole route length as soon as one
earlier route point and the target lie in the same original face. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Extending the final chord to time zero recovers its exact affine parametrization. -/
theorem recoveredSource_coordinates (P : ConvexPolyhedron) (F : P.Face)
    (t : unitInterval) (before : t < 1) (f : P.BoundaryCurve) :
    P.faceCoordinates F (f t) =
      AffineMap.lineMap (P.recoveredSource F t f) (P.faceCoordinates F (f 1)) (t : ℝ) := by
  have nonzero : 1 - (t : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr (show (t : ℝ) < 1 from before))
  rw [AffineMap.lineMap_apply_module, recoveredSource, smul_smul, mul_inv_cancel₀ nonzero, one_smul, sub_add_cancel]

/-- A cofacial terminal chord determines the distance from its recovered source to the target. -/
theorem recoveredSource_distance (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (geodesic : f ∈ P.geodesicCurves) (F : P.Face) (t : unitInterval) (before : t < 1)
    (inside : (f t : Space) ∈ F.val) (target : (f 1 : Space) ∈ F.val) :
    P.surfaceDist (f 0) (f 1) = dist (P.recoveredSource F t f) (P.faceCoordinates F (f 1)) := by
  have portion := geodesic t 1
  rw [P.surfaceDist_eq_dist_in_face F inside target,
    ← P.faceCoordinates_rigid F _ inside _ target,
    P.recoveredSource_coordinates F t before f, dist_lineMap_right] at portion
  have elapsed : dist t (1 : unitInterval) = 1 - (t : ℝ) := by
    change dist (t : ℝ) (1 : ℝ) = _
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr t.property.2)]
    ring
  rw [elapsed, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr t.property.2)] at portion
  have positive : 0 < 1 - (t : ℝ) := sub_pos.mpr (show (t : ℝ) < 1 from before)
  nlinarith

end SixVertexUnfolding.ConvexPolyhedron
