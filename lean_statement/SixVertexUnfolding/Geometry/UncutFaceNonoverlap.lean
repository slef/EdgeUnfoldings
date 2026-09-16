import SixVertexUnfolding.Geometry.FacePlanarMotions
import SixVertexUnfolding.Geometry.RetainedFaceContinuity
import SixVertexUnfolding.Geometry.Intersections

/-! An injective development gives nonoverlapping rigid original faces
whenever their interiors are uncut. Shared original edges have dimension
at most one and cannot account for an open overlap. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Distinct whole faces with uncut interiors have disjoint developed interiors. -/
theorem uncut_face_placements_nonoverlap {P : ConvexPolyhedron} {a : frontier P.body}
    (develop : P.UncutSurface a → Plane) (injective : Function.Injective develop)
    (F G : P.Face) (different : F ≠ G) (left right : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (left x) (left y) = dist x y)
    (right_rigid : ∀ x ∈ G.val, ∀ y ∈ G.val, dist (right x) (right y) = dist x y)
    (left_uncut : ∀ (x : Space) (hx : x ∈ F.val),
      P.faceCoordinates F x ∈ interior (P.faceCoordinates F '' F.val) →
      (⟨x, F.subset_frontier hx⟩ : frontier P.body) ∉ P.starCuts a)
    (right_uncut : ∀ (x : Space) (hx : x ∈ G.val),
      P.faceCoordinates G x ∈ interior (P.faceCoordinates G '' G.val) →
      (⟨x, G.subset_frontier hx⟩ : frontier P.body) ∉ P.starCuts a)
    (left_agrees : ∀ b : P.UncutSurface a, (b.val : Space) ∈ F.val → left b.val = develop b)
    (right_agrees : ∀ b : P.UncutSurface a, (b.val : Space) ∈ G.val → right b.val = develop b) :
    Disjoint (interior (left '' F.val)) (interior (right '' G.val)) := by
  let overlap := interior (left '' F.val) ∩ interior (right '' G.val)
  have contained : overlap ⊆ left '' (F.val ∩ G.val) := by
    intro z hz
    obtain ⟨x, xF, hx⟩ := interior_subset hz.1
    obtain ⟨y, yG, hy⟩ := interior_subset hz.2
    have x_inside := (F.placed_interior_iff left (P.faceCoordinates F)
      left_rigid (P.faceCoordinates_rigid F) xF).mp (hx.symm ▸ hz.1)
    have y_inside := (G.placed_interior_iff right (P.faceCoordinates G)
      right_rigid (P.faceCoordinates_rigid G) yG).mp (hy.symm ▸ hz.2)
    let b : P.UncutSurface a := ⟨⟨x, F.subset_frontier xF⟩, left_uncut x xF x_inside⟩
    let c : P.UncutSurface a := ⟨⟨y, G.subset_frontier yG⟩, right_uncut y yG y_inside⟩
    have same : b = c := injective
      ((left_agrees b xF).symm.trans (hx.trans (hy.symm.trans (right_agrees c yG))))
    have xy : x = y := congrArg (fun q : P.UncutSurface a => (q.val : Space)) same
    exact ⟨x, ⟨xF, xy.symm ▸ yG⟩, hx⟩
  have collinear : Collinear ℝ (F.val ∩ G.val) := by
    apply collinear_iff_finrank_le_one.mpr
    have dimension := F.intersection_dimension_le_one G different
    change Module.finrank ℝ (affineSpan ℝ (F.val ∩ G.val)).direction ≤ 1 at dimension
    rw [direction_affineSpan] at dimension
    exact dimension
  obtain ⟨p, v, on_line⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp collinear
  have image_collinear : Collinear ℝ (left '' (F.val ∩ G.val)) := by
    apply (collinear_iff_exists_forall_eq_smul_vadd _).mpr
    refine ⟨left p, left.linear v, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := on_line x hx
    exact ⟨r, by rw [left.map_vadd, map_smul]⟩
  apply disjoint_iff_inter_eq_empty.mpr
  apply not_nonempty_iff_eq_empty.mp
  intro nonempty
  obtain ⟨x, y, z, triangle⟩ := open_plane_contains_triangle overlap
    (isOpen_interior.inter isOpen_interior) nonempty
  apply triangle
  apply image_collinear.subset
  rintro q (rfl | rfl | rfl)
  exacts [contained x.property, contained y.property, contained z.property]

end SixVertexUnfolding.ConvexPolyhedron
