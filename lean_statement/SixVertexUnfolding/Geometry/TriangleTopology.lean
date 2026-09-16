import SixVertexUnfolding.Definitions

/-! A nondegenerate closed planar triangle is the closure of its ordinary planar interior. -/

namespace SixVertexUnfolding

/-- Three noncollinear planar points span the plane. -/
theorem planar_triangle_spans (a b c : Plane) (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Plane)) :
    affineSpan ℝ ({a, b, c} : Set Plane) = ⊤ := by
  have independent : AffineIndependent ℝ ![a, b, c] :=
    affineIndependent_iff_not_collinear_set.mpr noncollinear
  have spans := independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Plane])
  have points : Set.range ![a, b, c] = ({a, b, c} : Set Plane) := by
    ext x
    simp [Matrix.range_cons, Matrix.range_empty]
    tauto
  rwa [points] at spans

/-- Nondegenerate planar triangles have a nonempty two-dimensional interior. -/
theorem planar_triangle_interior_nonempty (a b c : Plane)
    (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Plane)) :
    (interior (convexHull ℝ ({a, b, c} : Set Plane))).Nonempty := by
  apply (convex_convexHull ℝ _).interior_nonempty_iff_affineSpan_eq_top.mpr
  rw [affineSpan_convexHull]
  exact planar_triangle_spans a b c noncollinear

/-- Every boundary point of a nondegenerate closed triangle is approached by interior points. -/
theorem planar_triangle_regular (a b c : Plane)
    (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Plane)) :
    closure (interior (convexHull ℝ ({a, b, c} : Set Plane))) = convexHull ℝ ({a, b, c} : Set Plane) := by
  rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior
    (planar_triangle_interior_nonempty a b c noncollinear)]
  exact (Set.toFinite ({a, b, c} : Set Plane)).isClosed_convexHull ℝ |>.closure_eq

end SixVertexUnfolding
