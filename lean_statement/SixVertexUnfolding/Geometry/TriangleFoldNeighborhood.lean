import SixVertexUnfolding.Geometry.TriangleChartRigidity
import SixVertexUnfolding.Geometry.RadialStripCornerGeometry

/-! A small planar corner of an actual triangle folds inside any
flat chart centered at its actual surface corner. -/

namespace SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle

open Set Filter Topology

variable {P : ConvexPolyhedron} {routes : C(unitInterval, P.BoundaryCurve)} {p l r : Plane}
    (D : RadialStripTriangle routes p l r)

/-- The neighborhood coverage of a flat chart applies to the continuous triangle folding. -/
theorem fold_near_left_in_chart {z : Space} (chart : P.FlatChart z)
    (at_center : (routes 0 1 : Space) = z) :
    ∃ ε > 0, ∀ x : convexHull ℝ ({p, l, r} : Set Plane), dist (x : Plane) l < ε →
      ((D.homeomorph.symm x).val : Space) ∈ chart.map '' chart.domain := by
  let corner : convexHull ℝ ({p, l, r} : Set Plane) :=
    ⟨l, subset_convexHull ℝ _ (by simp)⟩
  have folds : ((D.homeomorph.symm corner).val : Space) = (routes 0 1 : Space) :=
    congrArg (fun b : frontier P.body => (b : Space)) (D.fold_left_corner corner rfl)
  obtain ⟨U, openU, center, covered⟩ := chart.covers
  have near : ∀ᶠ x : convexHull ℝ ({p, l, r} : Set Plane) in 𝓝 corner,
      ((D.homeomorph.symm x).val : Space) ∈ U :=
    (continuous_subtype_val.comp (continuous_subtype_val.comp D.homeomorph.symm.continuous)).continuousAt.preimage_mem_nhds
      (openU.mem_nhds (by
        change ((D.homeomorph.symm corner).val : Space) ∈ U
        rw [folds, at_center]
        exact center))
  obtain ⟨ε, positive, inside⟩ := Metric.eventually_nhds_iff.mp near
  exact ⟨ε, positive, fun x hx => covered ⟨inside hx, (D.homeomorph.symm x).val.property⟩⟩

end SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle
