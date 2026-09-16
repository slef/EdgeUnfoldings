import SixVertexUnfolding.Geometry.RadialStripDevelopments
import SixVertexUnfolding.Geometry.NonexpandingSegments

/-! Every radial triangle folds exactly radially near each of its points,
including its corners at original polyhedron vertices. This uses its
proved finite rigid face pieces; it does not assume a flat vertex chart. -/

namespace SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle

open Set

variable {P : ConvexPolyhedron} {routes : C(unitInterval, P.BoundaryCurve)} {p l r : Plane}
  (D : RadialStripTriangle routes p l r)

/-- The first base corner folds to the endpoint of the first limiting route. -/
theorem fold_left_corner (corner : convexHull ℝ ({p, l, r} : Set Plane))
    (at_left : (corner : Plane) = l) :
    (D.homeomorph.symm corner).val = routes 0 1 := by
  let x : range (closedRouteStripMap routes) := ⟨closedRouteStripMap routes (0, 1), mem_range_self _⟩
  have placed : (D.homeomorph x : Plane) = l := by
    simpa [x, triangleFanMap] using D.radial (0, 1)
  have equal : D.homeomorph x = corner := Subtype.ext (placed.trans at_left.symm)
  rw [← equal, D.homeomorph.symm_apply_apply]
  rfl

/-- A sufficiently small neighborhood preserves distance from the chosen center. -/
theorem local_radial_distance (x : convexHull ℝ ({p, l, r} : Set Plane)) :
    ∃ ε > 0, ∀ y : convexHull ℝ ({p, l, r} : Set Plane), dist (y : Plane) x < ε →
      dist ((D.homeomorph.symm y).val : Space) ((D.homeomorph.symm x).val : Space) =
        dist (y : Plane) x :=
  D.rigid_pieces.local_radial_distance
    (continuous_subtype_val.comp (continuous_subtype_val.comp D.homeomorph.symm.continuous)) x

/-- The same local distance identity, with neighborhoods measured on the actual surface. -/
theorem local_radial_distance_forward (x : range (closedRouteStripMap routes)) :
    ∃ δ > 0, ∀ y : range (closedRouteStripMap routes),
      dist (y.val : Space) (x.val : Space) < δ →
        dist (D.homeomorph y : Plane) (D.homeomorph x : Plane) =
          dist (y.val : Space) (x.val : Space) := by
  obtain ⟨ε, positive, radial⟩ := D.local_radial_distance (D.homeomorph x)
  have continuous := continuous_subtype_val.comp D.homeomorph.continuous
  obtain ⟨δ, dp, near⟩ := Metric.continuousAt_iff.mp continuous.continuousAt ε positive
  refine ⟨δ, dp, ?_⟩
  intro y small
  have equal := radial (D.homeomorph y) (near small)
  simpa only [D.homeomorph.symm_apply_apply] using equal.symm

/-- At the first base endpoint, use its actual limiting route endpoint
as the spatial center and its metric base corner as the planar center. -/
theorem left_radial_distance :
    ∃ ε > 0, ∀ y : range (closedRouteStripMap routes),
      dist (y.val : Space) (routes 0 1 : Space) < ε →
        dist (D.homeomorph y : Plane) l = dist (y.val : Space) (routes 0 1 : Space) := by
  let x : range (closedRouteStripMap routes) := ⟨closedRouteStripMap routes (0, 1), mem_range_self _⟩
  have placed : (D.homeomorph x : Plane) = l := by
    simpa [x, triangleFanMap] using D.radial (0, 1)
  obtain ⟨ε, positive, radial⟩ := D.local_radial_distance_forward x
  refine ⟨ε, positive, ?_⟩
  intro y near
  have equal := radial y near
  rwa [placed] at equal

/-- Small radial segments fold to the actual straight spatial segments
from the center, with the same affine parameter. -/
theorem local_radial_segments (x : convexHull ℝ ({p, l, r} : Set Plane)) :
    ∃ ε > 0, ∀ y : convexHull ℝ ({p, l, r} : Set Plane), dist (y : Plane) x < ε →
      ∀ (t : ℝ) (between : t ∈ Icc (0 : ℝ) 1),
        let z : convexHull ℝ ({p, l, r} : Set Plane) :=
          ⟨AffineMap.lineMap (x : Plane) y t,
            (convex_convexHull ℝ _).mapsTo_lineMap x.property y.property between⟩
        ((D.homeomorph.symm z).val : Space) = AffineMap.lineMap
          ((D.homeomorph.symm x).val : Space) ((D.homeomorph.symm y).val : Space) t := by
  obtain ⟨ε, positive, radial⟩ := D.local_radial_distance x
  refine ⟨ε, positive, ?_⟩
  intro y near t between
  exact nonexpanding_lineMap (convex_convexHull ℝ _)
    (fun z => ((D.homeomorph.symm z).val : Space)) D.inverse_nonexpanding x y
    (by rw [dist_comm, radial y near, dist_comm (y : Plane) (x : Plane)]) t between

end SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle
