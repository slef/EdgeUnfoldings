import SixVertexUnfolding.Geometry.FiniteSourceImages
import SixVertexUnfolding.Geometry.EdgeUnfoldingInverse

/-! Source copies from either incident face are placed in one joined planar
development of an original edge. The resulting candidate set is finite. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G)

/-- Move canonical first-face coordinates to this edge development. -/
noncomputable def firstMotion : Plane →ᵃ[ℝ] Plane :=
  (F.exists_coordinate_change (P.faceCoordinates F) chart.left (P.faceCoordinates_rigid F)
    (fun x hx y hy => chart.left_rigid x (subset_affineSpan ℝ _ hx) y (subset_affineSpan ℝ _ hy))).choose

/-- Move canonical second-face coordinates to this same edge development. -/
noncomputable def secondMotion : Plane →ᵃ[ℝ] Plane :=
  (G.exists_coordinate_change (P.faceCoordinates G) chart.right (P.faceCoordinates_rigid G)
    (fun x hx y hy => chart.right_rigid x (subset_affineSpan ℝ _ hx) y (subset_affineSpan ℝ _ hy))).choose

theorem firstMotion_rigid (x y : Plane) : dist (chart.firstMotion x) (chart.firstMotion y) = dist x y :=
  (F.exists_coordinate_change (P.faceCoordinates F) chart.left (P.faceCoordinates_rigid F)
    (fun x hx y hy => chart.left_rigid x (subset_affineSpan ℝ _ hx) y (subset_affineSpan ℝ _ hy))).choose_spec.1 x y

theorem secondMotion_rigid (x y : Plane) : dist (chart.secondMotion x) (chart.secondMotion y) = dist x y :=
  (G.exists_coordinate_change (P.faceCoordinates G) chart.right (P.faceCoordinates_rigid G)
    (fun x hx y hy => chart.right_rigid x (subset_affineSpan ℝ _ hx) y (subset_affineSpan ℝ _ hy))).choose_spec.1 x y

theorem firstMotion_on_face (x : Space) (hx : x ∈ F.val) :
    chart.firstMotion (P.faceCoordinates F x) = chart.left x :=
  (F.exists_coordinate_change (P.faceCoordinates F) chart.left (P.faceCoordinates_rigid F)
    (fun x hx y hy => chart.left_rigid x (subset_affineSpan ℝ _ hx) y (subset_affineSpan ℝ _ hy))).choose_spec.2 x hx

theorem secondMotion_on_face (x : Space) (hx : x ∈ G.val) :
    chart.secondMotion (P.faceCoordinates G x) = chart.right x :=
  (G.exists_coordinate_change (P.faceCoordinates G) chart.right (P.faceCoordinates_rigid G)
    (fun x hx y hy => chart.right_rigid x (subset_affineSpan ℝ _ hx) y (subset_affineSpan ℝ _ hy))).choose_spec.2 x hx

/-- The two finite candidate lists, expressed in the same planar coordinates. -/
noncomputable def sourceImages (a : Space) : Set Plane :=
  chart.firstMotion '' P.sourceImages a F ∪ chart.secondMotion '' P.sourceImages a G

theorem sourceImages_finite (a : Space) : (chart.sourceImages a).Finite :=
  ((P.sourceImages_finite a F).image chart.firstMotion).union
    ((P.sourceImages_finite a G).image chart.secondMotion)

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
