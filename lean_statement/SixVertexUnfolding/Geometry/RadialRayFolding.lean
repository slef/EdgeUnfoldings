import SixVertexUnfolding.Geometry.RadialStripDevelopments
import SixVertexUnfolding.Geometry.TwoClosedFoldings
import SixVertexUnfolding.Geometry.JoinedTriangles

/-! Two radial triangles on opposite sides of their shared endpoint
ray have one continuous actual folding across the whole retained ray. -/

namespace SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle

open Set

variable {P : ConvexPolyhedron}
    {routes other : C(unitInterval, P.BoundaryCurve)} {p l r q u v : Plane}
    (D : RadialStripTriangle routes p l r) (E : RadialStripTriangle other q u v)

theorem fold_on_left_ray (t : unitInterval)
    (inside : AffineMap.lineMap p l (t : ℝ) ∈ convexHull ℝ ({p, l, r} : Set Plane)) :
    (D.homeomorph.symm ⟨_, inside⟩).val = routes 0 t := by
  have placed : D.homeomorph ⟨closedRouteStripMap routes (0, t), mem_range_self _⟩ = ⟨_, inside⟩ := by
    apply Subtype.ext
    simpa [triangleFanMap] using D.radial (0, t)
  rw [← placed, D.homeomorph.symm_apply_apply]
  rfl

/-- Complete inverse foldings paste across the common source-to-junction segment. -/
theorem glue_left_ray (same_route : routes 0 = other 0) (same_source : p = q) (same_root : l = u)
    (opposite : det (p - l) (r - l) * det (q - u) (v - u) < 0) :
    ∃ fold : C((convexHull ℝ ({p, l, r} : Set Plane) ∪ convexHull ℝ ({q, u, v} : Set Plane) : Set Plane), frontier P.body),
      (∀ x : convexHull ℝ ({p, l, r} : Set Plane),
        fold ⟨x, Or.inl x.property⟩ = (D.homeomorph.symm x).val) ∧
      (∀ x : convexHull ℝ ({q, u, v} : Set Plane),
        fold ⟨x, Or.inr x.property⟩ = (E.homeomorph.symm x).val) ∧
      HasFiniteRigidPieces _ (fun x => (fold x : Space)) := by
  subst q
  subst u
  have intersection : convexHull ℝ ({p, l, r} : Set Plane) ∩ convexHull ℝ ({p, l, v} : Set Plane) =
      segment ℝ p l := by
    simpa only [insert_comm p l, segment_symm ℝ p l] using opposite_triangles_intersection l p r v opposite
  let f : C(convexHull ℝ ({p, l, r} : Set Plane), frontier P.body) :=
    ⟨fun x => (D.homeomorph.symm x).val, continuous_subtype_val.comp D.homeomorph.symm.continuous⟩
  let g : C(convexHull ℝ ({p, l, v} : Set Plane), frontier P.body) :=
    ⟨fun x => (E.homeomorph.symm x).val, continuous_subtype_val.comp E.homeomorph.symm.continuous⟩
  have compatible (x : Plane) (hx : x ∈ convexHull ℝ ({p, l, r} : Set Plane))
      (hy : x ∈ convexHull ℝ ({p, l, v} : Set Plane)) : f ⟨x, hx⟩ = g ⟨x, hy⟩ := by
    have on_ray : x ∈ segment ℝ p l := intersection ▸ ⟨hx, hy⟩
    rw [segment_eq_image_lineMap] at on_ray
    obtain ⟨t, unit, rfl⟩ := on_ray
    exact (D.fold_on_left_ray ⟨t, unit⟩ hx).trans
      ((congrArg (fun route : P.BoundaryCurve => route ⟨t, unit⟩) same_route).trans
        (E.fold_on_left_ray ⟨t, unit⟩ hy).symm)
  have closed (p l r : Plane) : IsClosed (convexHull ℝ ({p, l, r} : Set Plane)) := by
    have finite : ({p, l, r} : Set Plane).Finite := by simp
    exact (finite.isCompact_convexHull ℝ).isClosed
  obtain ⟨fold, on_left, on_right⟩ := glue_two_closed_foldings _ _ (closed p l r) (closed p l v) f g compatible
  refine ⟨fold, on_left, on_right, ?_⟩
  apply finite_rigid_pieces_union
  · convert D.rigid_pieces using 1
    funext x
    exact congrArg (fun b : frontier P.body => (b : Space)) (on_left x)
  · convert E.rigid_pieces using 1
    funext x
    exact congrArg (fun b : frontier P.body => (b : Space)) (on_right x)

end SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle
