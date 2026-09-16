import SixVertexUnfolding.Geometry.NonexpandingRigidity
import SixVertexUnfolding.Geometry.RadialStripDevelopments
import SixVertexUnfolding.Geometry.FlatChartCoordinates

/-! Agreement at small corner triangles extends to their whole interiors.
The distance bound comes from the actual folded surface paths. -/

namespace SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle

open Set

variable {P : ConvexPolyhedron} {routes : C(unitInterval, P.BoundaryCurve)} {p l r : Plane}
    (D : RadialStripTriangle routes p l r)

/-- On a convex subregion that folds into a flat chart, inverse coordinates do not expand. -/
theorem folding_coordinates_nonexpanding {z : Space} (chart : P.FlatChart z)
    (region : Set Plane) (contained : region ⊆ convexHull ℝ ({p, l, r} : Set Plane))
    (in_chart : ∀ x : region,
      ((D.homeomorph.symm ⟨x, contained x.property⟩).val : Space) ∈ chart.map '' chart.domain) :
    LipschitzWith 1 (fun x : region =>
      chart.coordinates ((D.homeomorph.symm ⟨x, contained x.property⟩).val : Space)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [chart.coordinates_distance (in_chart x) (in_chart y)]
  simpa only [NNReal.coe_one, one_mul] using
    D.surface_distance_le ⟨x, contained x.property⟩ ⟨y, contained y.property⟩

/-- Agreement at every generating corner gives agreement on their entire convex hull. -/
theorem fold_eq_chart_on_hull {z : Space} (chart : P.FlatChart z) (corners : Set Plane)
    (contained : convexHull ℝ corners ⊆ convexHull ℝ ({p, l, r} : Set Plane))
    (in_chart : ∀ x : convexHull ℝ corners,
      ((D.homeomorph.symm ⟨x, contained x.property⟩).val : Space) ∈ chart.map '' chart.domain)
    (corners_in_domain : corners ⊆ chart.domain)
    (agrees : ∀ x (member : x ∈ corners),
      ((D.homeomorph.symm ⟨x, contained (subset_convexHull ℝ corners member)⟩).val : Space) = chart.map x) :
    ∀ x : convexHull ℝ corners,
      ((D.homeomorph.symm ⟨x, contained x.property⟩).val : Space) = chart.map x := by
  let f (x : convexHull ℝ corners) :=
    chart.coordinates ((D.homeomorph.symm ⟨x, contained x.property⟩).val : Space)
  have fixed := nonexpanding_eq_on_convexHull corners (convexHull ℝ corners)
    (convex_convexHull ℝ _) (subset_convexHull ℝ _) f
    (D.folding_coordinates_nonexpanding chart _ contained in_chart) (by
      intro x member
      dsimp [f]
      rw [agrees x member, chart.coordinates_map (corners_in_domain member)])
  intro x
  have at_x : chart.coordinates ((D.homeomorph.symm ⟨x, contained x.property⟩).val : Space) = x :=
    fixed x x.property
  exact (chart.map_coordinates (in_chart x)).symm.trans (congrArg chart.map at_x)

end SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle
