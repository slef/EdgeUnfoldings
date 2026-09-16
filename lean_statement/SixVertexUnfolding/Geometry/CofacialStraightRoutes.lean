import SixVertexUnfolding.Geometry.CofacialStarCuts

/-! The straight segments used in the star-cut definition are exactly
the traces of normalized shortest routes to the cofacial vertices. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A straight face segment is a normalized geodesic, with its exact parametrization. -/
theorem exists_straight_geodesic (P : ConvexPolyhedron) (a b : frontier P.body)
    (F : P.Face) (source : (a : Space) ∈ F.val) (target : (b : Space) ∈ F.val) :
    ∃ route : P.BoundaryCurve, route ∈ P.geodesicFiber a b ∧
      ∀ t : unitInterval, (route t : Space) = AffineMap.lineMap (a : Space) (b : Space) (t : ℝ) := by
  let path := SurfacePath.inFace F source target
  let route := path.boundaryCurve
  have point (t : unitInterval) : (route t : Space) =
      AffineMap.lineMap (a : Space) (b : Space) (t : ℝ) := rfl
  have on_face (t : unitInterval) : (route t : Space) ∈ F.val := by
    rw [point]
    exact F.convex.segment_subset source target (by
      rw [segment_eq_image_lineMap]
      exact ⟨t, t.property, rfl⟩)
  have first : route 0 = a := Subtype.ext path.curve.source
  have last : route 1 = b := Subtype.ext path.curve.target
  refine ⟨route, ⟨?_, Prod.ext first last⟩, point⟩
  intro s t
  rw [P.surfaceDist_eq_dist_in_face F (on_face s) (on_face t), first, last,
    P.surfaceDist_eq_dist_in_face F source target, point s, point t, dist_lineMap_lineMap]
  change dist (s : ℝ) (t : ℝ) * dist (a : Space) (b : Space) =
    dist (a : Space) (b : Space) * dist (s : ℝ) (t : ℝ)
  exact mul_comm _ _

/-- Every point of a cofacial source-to-vertex segment lies on an actual shortest ray. -/
theorem exists_original_ray_through_cut (P : ConvexPolyhedron) (a : frontier P.body)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {x : frontier P.body} (on_cut : x ∈ P.starCuts a) :
    ∃ b : frontier P.body, (b : Space) ∈ P.vertices ∧
      ∃ route : P.BoundaryCurve, route ∈ P.geodesicFiber a b ∧ x ∈ range route := by
  obtain ⟨v, segment_member⟩ := on_cut
  obtain ⟨F, source, target⟩ := cofacial v
  let b : frontier P.body := ⟨v, F.subset_frontier target⟩
  obtain ⟨route, member, straight⟩ := P.exists_straight_geodesic a b F source target
  rw [segment_eq_image_lineMap] at segment_member
  obtain ⟨t, unit, at_x⟩ := segment_member
  refine ⟨b, v.property, route, member, ⟨⟨t, unit⟩, ?_⟩⟩
  exact Subtype.ext ((straight ⟨t, unit⟩).trans at_x)

end SixVertexUnfolding.ConvexPolyhedron
