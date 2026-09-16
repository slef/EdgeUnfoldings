import SixVertexUnfolding.Geometry.FiniteRigidPieces
import SixVertexUnfolding.Geometry.ConvexFiniteSelection
import SixVertexUnfolding.Geometry.ConvexSurfaceFolding

/-! A continuous finite rigid folding cannot increase the length
of a straight segment lying inside its planar domain. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

theorem finite_folding_on_convex_patch {P : ConvexPolyhedron} {region : Set Plane}
    (fold : C(region, frontier P.body))
    (pieces : HasFiniteRigidPieces region (fun x => (fold x : Space)))
    (patch : Set Plane) (convex_patch : Convex ℝ patch) (contained : patch ⊆ region) :
    LipschitzWith 1 (fun x : patch => (fold ⟨x, contained x.property⟩ : Space)) := by
  obtain ⟨maps, finite_maps, rigid, selected⟩ := pieces
  letI : Finite maps := finite_maps.to_subtype
  apply convex_subtype_finite_selection_lipschitz patch convex_patch
    (fun x : patch => (fold ⟨x, contained x.property⟩ : Space)) (fun f : maps => f.val) 1
  · exact continuous_subtype_val.comp (fold.continuous.comp (continuous_subtype_val.subtype_mk _))
  · intro f
    exact (rigid f.val f.property).lipschitz.lipschitzOnWith
  · intro x
    obtain ⟨f, member, same⟩ := selected ⟨x, contained x.property⟩
    exact ⟨⟨f, member⟩, same⟩

/-- This comparison concerns actual intrinsic surface distance. -/
theorem finite_folding_segment_distance {P : ConvexPolyhedron} {region : Set Plane}
    (fold : C(region, frontier P.body))
    (pieces : HasFiniteRigidPieces region (fun x => (fold x : Space)))
    (x y : region) (contained : segment ℝ (x : Plane) (y : Plane) ⊆ region) :
    P.surfaceDist (fold x) (fold y) ≤ dist (x : Plane) (y : Plane) := by
  let patch := segment ℝ (x : Plane) (y : Plane)
  let restriction : C(patch, frontier P.body) :=
    ⟨fun z => fold ⟨z, contained z.property⟩,
      fold.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  have bound := finite_folding_on_convex_patch fold pieces patch (convex_segment _ _) contained
  exact convex_folding_surface_distance patch (convex_segment _ _) restriction bound
    ⟨x, left_mem_segment ℝ _ _⟩ ⟨y, right_mem_segment ℝ _ _⟩

end SixVertexUnfolding.ConvexPolyhedron
