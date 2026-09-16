import SixVertexUnfolding.Geometry.EdgeUnfoldingInverse
import SixVertexUnfolding.Geometry.SurfaceDistance

/-! Straight segments in a local edge development lift to actual surface
paths of exactly the same length, including segments crossing the crease. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.Neighborhood

open Set
open scoped ENNReal NNReal

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} {chart : EdgeFolding facets F G} {z : Space} (near : chart.Neighborhood z)

theorem on_facets {x : Plane} (hx : x ∈ near.domain) : chart.fold.map x ∈ F.val ∪ G.val := by
  by_cases positive : 0 ≤ chart.fold.height x
  · rw [chart.fold.map_of_nonnegative positive]
    exact Or.inl (near.first_in x hx positive)
  · rw [chart.fold.map_of_nonpositive (le_of_not_ge positive)]
    exact Or.inr (near.second_in x hx (le_of_not_ge positive))

/-- Lift a whole planar segment contained in this neighborhood onto the boundary. -/
noncomputable def segmentPath (x y : Plane) (inside : segment ℝ x y ⊆ near.domain) :
    P.SurfacePath (chart.fold.map x) (chart.fold.map y) where
  curve := {
    toFun := fun t => chart.fold.map (Path.segment x y t)
    continuous_toFun := chart.fold.continuous.comp (Path.segment x y).continuous
    source' := by simp
    target' := by simp }
  on_surface t := near.on_surface ⟨Path.segment x y t,
    inside (by rw [← Path.range_segment]; exact ⟨t, rfl⟩), rfl⟩

/-- The folded segment retains the usual planar constant-speed upper bound. -/
theorem segmentPath_lipschitz (x y : Plane) (inside : segment ℝ x y ⊆ near.domain) :
    LipschitzWith (nndist x y) (near.segmentPath x y inside).curve := by
  have speed : LipschitzWith (nndist x y) (Path.segment x y) := by
    have bound := (lipschitzWith_lineMap x y (𝕜 := ℝ)).comp
      (isometry_subtype_coe : Isometry ((↑) : unitInterval → ℝ)).lipschitz
    simpa only [mul_one] using bound
  simpa only [one_mul] using chart.fold.lipschitz.comp speed

/-- The lifted segment has precisely its planar length. -/
theorem segmentPath_length (x y : Plane) (inside : segment ℝ x y ⊆ near.domain) :
    (near.segmentPath x y inside).length = edist x y := by
  apply le_antisymm
  · simpa only [edist_nndist] using (near.segmentPath x y inside).length_le_of_lipschitz
      (near.segmentPath_lipschitz x y inside)
  · have lower := chart.unfolded_chord_le_length (near.segmentPath x y inside) (fun t =>
      near.on_facets (inside (by rw [← Path.range_segment]; exact ⟨t, rfl⟩)))
    rwa [Neighborhood.unfold_fold chart near (inside (left_mem_segment ℝ x y)),
      Neighborhood.unfold_fold chart near (inside (right_mem_segment ℝ x y))] at lower

/-- Intrinsic distance between points in a convex chart region is no greater than their planar distance. -/
theorem surfaceDist_le_planar (x y : Plane) (inside : segment ℝ x y ⊆ near.domain) :
    P.surfaceDist (chart.fold.map x) (chart.fold.map y) ≤ dist x y := by
  have bound := (near.segmentPath x y inside).surfaceEDist_le_length
  rw [near.segmentPath_length x y inside] at bound
  have real_bound := ENNReal.toReal_mono (edist_ne_top x y) bound
  simpa only [surfaceDist, edist_dist, ENNReal.toReal_ofReal dist_nonneg] using real_bound

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.Neighborhood
