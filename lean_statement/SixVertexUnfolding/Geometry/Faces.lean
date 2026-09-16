import SixVertexUnfolding.Geometry.Polyhedron

/-! The supporting-plane definition gives actual finite convex polygonal faces. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F : P.Face)

theorem subset_body : F.val ⊆ P.body := by
  obtain ⟨_, n, h, _, _, face_eq⟩ := F.property
  rw [face_eq]
  exact fun _ hx => hx.1

theorem nonempty : F.val.Nonempty := by
  by_contra empty
  have face_empty := Set.not_nonempty_iff_eq_empty.mp empty
  have dimension_two := F.property.1
  change affineDimension F.val = 2 at dimension_two
  rw [face_empty] at dimension_two
  rw [affineDimension, AffineSubspace.span_empty, AffineSubspace.direction_bot] at dimension_two
  norm_num at dimension_two

/-- A supporting face is exposed in Mathlib's sense. -/
theorem isExposed : IsExposed ℝ P.body F.val := by
  obtain ⟨_, n, h, _, support, face_eq⟩ := F.property
  intro _
  refine ⟨innerSL ℝ n, ?_⟩
  obtain ⟨z, hz⟩ := F.nonempty
  rw [face_eq] at hz ⊢
  ext x
  constructor
  · rintro ⟨hx, height⟩
    exact ⟨hx, fun y hy => by simpa [height] using support y hy⟩
  · rintro ⟨hx, maximal⟩
    refine ⟨hx, le_antisymm (support x hx) ?_⟩
    simpa [hz.2] using maximal z hz.1

theorem isCompact : IsCompact F.val :=
  F.isExposed.isCompact P.body_compact

theorem isClosed : IsClosed F.val :=
  F.isCompact.isClosed

theorem convex : Convex ℝ F.val := by
  obtain ⟨_, n, h, _, _, face_eq⟩ := F.property
  rw [face_eq]
  exact P.body_convex.inter (convex_hyperplane
    ⟨fun x y => inner_add_right n x y, fun a x => inner_smul_right n x a⟩ h)

/-- The vertices of a face are precisely the solid's vertices lying on it. -/
theorem extreme_points : F.val.extremePoints ℝ = F.val ∩ (P.vertices : Set Space) := by
  rw [F.isExposed.isExtreme.extremePoints_eq, P.body_extreme_points]

theorem extreme_points_finite : (F.val.extremePoints ℝ).Finite := by
  rw [F.extreme_points]
  exact P.vertices.finite_toSet.subset Set.inter_subset_right

/-- Each face is the convex hull of its original vertices; no triangulation is assumed. -/
theorem eq_convexHull_vertices :
    F.val = convexHull ℝ (F.val ∩ (P.vertices : Set Space)) := by
  have hull_closed := F.extreme_points_finite.isClosed_convexHull ℝ
  have hull_eq := closure_convexHull_extremePoints F.isCompact F.convex
  rw [hull_closed.closure_eq, F.extreme_points] at hull_eq
  exact hull_eq.symm

/-- In particular, a face is determined by its original vertex set. -/
theorem eq_of_same_vertices (G : P.Face)
    (same : F.val ∩ (P.vertices : Set Space) = G.val ∩ (P.vertices : Set Space)) : F = G := by
  apply Subtype.ext
  rw [F.eq_convexHull_vertices, G.eq_convexHull_vertices, same]

/-- The apparent set-valued face type is finite: each face has a distinct vertex subset. -/
instance finite_faces (P : ConvexPolyhedron) : Finite P.Face := by
  classical
  let verticesOnFace (F : P.Face) : Set (P.vertices : Set Space) :=
    {x | (x : Space) ∈ F.val}
  apply Finite.of_injective verticesOnFace
  intro F G same
  apply F.eq_of_same_vertices G
  ext x
  constructor
  · rintro ⟨hxF, hxP⟩
    have membership := Set.ext_iff.mp same ⟨x, hxP⟩
    exact ⟨membership.mp hxF, hxP⟩
  · rintro ⟨hxG, hxP⟩
    have membership := Set.ext_iff.mp same ⟨x, hxP⟩
    exact ⟨membership.mpr hxG, hxP⟩

end SixVertexUnfolding.ConvexPolyhedron.Face
