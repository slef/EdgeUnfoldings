import SixVertexUnfolding.Geometry.SurfaceDistance
import SixVertexUnfolding.Geometry.SurfaceReparameterization
import Mathlib.Analysis.Convex.Basic

/-! A nonexpanding map from a convex planar region to the surface
also bounds intrinsic surface distances: lift the straight planar segment. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set
open scoped NNReal ENNReal

/-- Folding a straight planar segment supplies a surface route of no greater length. -/
theorem convex_folding_surface_distance {P : ConvexPolyhedron}
    (region : Set Plane) (convex_region : Convex ℝ region)
    (fold : C(region, frontier P.body))
    (nonexpanding : LipschitzWith 1 (fun z => (fold z : Space))) (x y : region) :
    P.surfaceDist (fold x) (fold y) ≤ dist (x : Plane) (y : Plane) := by
  let line : C(unitInterval, region) :=
    ⟨fun t => ⟨AffineMap.lineMap (x : Plane) (y : Plane) (t : ℝ),
      convex_region.lineMap_mem x.property y.property t.property⟩,
      (((lipschitzWith_lineMap (x : Plane) (y : Plane)).continuous.comp continuous_subtype_val).subtype_mk _)⟩
  have first : line 0 = x := Subtype.ext (AffineMap.lineMap_apply_zero _ _)
  have last : line 1 = y := Subtype.ext (AffineMap.lineMap_apply_one _ _)
  let path : P.SurfacePath (fold x) (fold y) := {
    curve := {
      toFun := fun t => (fold (line t) : Space)
      continuous_toFun := continuous_subtype_val.comp (fold.continuous.comp line.continuous)
      source' := by rw [first]
      target' := by rw [last] }
    on_surface := fun t => (fold (line t)).property }
  have speed : LipschitzWith (nndist (x : Plane) (y : Plane)) path.curve := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have bound := nonexpanding.dist_le_mul (line s) (line t)
    change dist (fold (line s) : Space) (fold (line t) : Space) ≤ _
    change dist (fold (line s) : Space) (fold (line t) : Space) ≤
      (1 : ℝ) * dist (AffineMap.lineMap (x : Plane) (y : Plane) (s : ℝ))
        (AffineMap.lineMap (x : Plane) (y : Plane) (t : ℝ)) at bound
    simpa only [one_mul, dist_lineMap_lineMap, coe_nndist, mul_comm] using bound
  have upper := path.surfaceEDist_le_length.trans (path.length_le_of_lipschitz speed)
  have real_bound := ENNReal.toReal_mono ENNReal.coe_ne_top upper
  simpa only [surfaceDist, ENNReal.coe_toReal, coe_nndist] using real_bound

end SixVertexUnfolding.ConvexPolyhedron
