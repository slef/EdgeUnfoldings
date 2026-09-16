import SixVertexUnfolding.Geometry.EdgeGraph
import SixVertexUnfolding.Geometry.StrictSupport

/-!
Look from a vertex at a transverse plane. Rays to the other vertices meet that plane
in a finite set; its convex hull is the vertex figure. Its corners will certify edges.
-/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- A strictly supporting normal supplies the transverse plane for the vertex figure. -/
structure VertexFigure (P : ConvexPolyhedron) (v : P.Vertex) where
  normal : Space
  strict : ∀ w ∈ P.vertices, w ≠ (v : Space) → inner ℝ normal w < inner ℝ normal v

namespace VertexFigure

variable {P : ConvexPolyhedron} {v : P.Vertex} (figure : VertexFigure P v)

noncomputable def gap (w : Space) : ℝ :=
  inner ℝ figure.normal v - inner ℝ figure.normal w

/-- Translate the vertex to the origin and intersect each outgoing ray with height minus one. -/
noncomputable def direction (w : Space) : Space :=
  (figure.gap w)⁻¹ • (w - v)

def points : Set Space :=
  figure.direction '' ((P.vertices : Set Space) \ {(v : Space)})

def corners : Set Space := (convexHull ℝ figure.points).extremePoints ℝ

theorem gap_pos {w : Space} (vertex : w ∈ P.vertices) (distinct : w ≠ (v : Space)) :
    0 < figure.gap w := sub_pos.mpr (figure.strict w vertex distinct)

theorem reconstruct {w : Space} (vertex : w ∈ P.vertices) (distinct : w ≠ (v : Space)) :
    figure.gap w • figure.direction w = w - v := by
  rw [direction, smul_smul, mul_inv_cancel₀ (figure.gap_pos vertex distinct).ne', one_smul]

theorem direction_height {w : Space} (vertex : w ∈ P.vertices)
    (distinct : w ≠ (v : Space)) : inner ℝ figure.normal (figure.direction w) = -1 := by
  have nonzero := (figure.gap_pos vertex distinct).ne'
  rw [direction, inner_smul_right, inner_sub_right]
  rw [show inner ℝ figure.normal w - inner ℝ figure.normal v = -(figure.gap w) by
    simp [gap]]
  simp [nonzero]

theorem points_finite : figure.points.Finite :=
  P.vertices.finite_toSet.diff.image figure.direction

theorem points_height {p : Space} (member : p ∈ figure.points) :
    inner ℝ figure.normal p = -1 := by
  obtain ⟨w, ⟨vertex, distinct⟩, rfl⟩ := member
  exact figure.direction_height vertex distinct

/-- Different original vertices lie on different rays from v. -/
theorem direction_injective :
    Set.InjOn figure.direction ((P.vertices : Set Space) \ {(v : Space)}) := by
  intro a ha b hb same
  by_contra distinct
  apply P.no_three_collinear_vertices v.property ha.1 hb.1 (Ne.symm ha.2) (Ne.symm hb.2)
    distinct
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨(v : Space), figure.direction a, ?_⟩
  intro p hp
  rcases hp with hp | hp | hp
  · subst p
    exact ⟨0, by simp⟩
  · subst p
    exact ⟨figure.gap a, by simpa using (eq_add_of_sub_eq (figure.reconstruct ha.1 ha.2).symm)⟩
  · have equal : p = b := hp
    subst p
    refine ⟨figure.gap b, ?_⟩
    rw [same]
    simpa using (eq_add_of_sub_eq (figure.reconstruct hb.1 hb.2).symm)

/-- The outgoing rays span all three spatial directions. -/
theorem points_span : Submodule.span ℝ figure.points = ⊤ := by
  have original_span : vectorSpan ℝ (P.vertices : Set Space) = ⊤ :=
    AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ Space Space P.vertices_span_space
  rw [vectorSpan_eq_span_vsub_set_right ℝ v.property] at original_span
  apply top_unique
  rw [← original_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨w, vertex, rfl⟩
  by_cases same : w = (v : Space)
  · simp [same]
  · change w - (v : Space) ∈ Submodule.span ℝ figure.points
    rw [← figure.reconstruct vertex same]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, ⟨vertex, same⟩, rfl⟩)

theorem corners_subset_points : figure.corners ⊆ figure.points :=
  extremePoints_convexHull_subset

theorem corners_finite : figure.corners.Finite :=
  figure.points_finite.subset figure.corners_subset_points

theorem corners_hull : convexHull ℝ figure.corners = convexHull ℝ figure.points := by
  have hull := closure_convexHull_extremePoints (figure.points_finite.isCompact_convexHull ℝ)
    (convex_convexHull ℝ figure.points)
  change closure (convexHull ℝ figure.corners) = convexHull ℝ figure.points at hull
  rwa [figure.corners_finite.isClosed_convexHull ℝ |>.closure_eq] at hull

theorem corners_span : Submodule.span ℝ figure.corners = ⊤ := by
  apply top_unique
  rw [← figure.points_span]
  apply Submodule.span_le.mpr
  have hull_in_span : convexHull ℝ figure.corners ⊆ Submodule.span ℝ figure.corners :=
    convexHull_min Submodule.subset_span (Submodule.convex _)
  intro p hp
  apply hull_in_span
  rw [figure.corners_hull]
  exact subset_convexHull ℝ _ hp

/-- A vertex figure has at least three corners. -/
theorem three_le_corner_count : 3 ≤ Nat.card figure.corners := by
  letI : Fintype figure.corners := figure.corners_finite.fintype
  have span : Submodule.span ℝ (Set.range (fun p : figure.corners => (p : Space))) = ⊤ := by
    rw [Subtype.range_coe]
    exact figure.corners_span
  have bound := finrank_le_of_span_eq_top span
  simpa [Space, Nat.card_eq_fintype_card] using bound

end VertexFigure
end SixVertexUnfolding.ConvexPolyhedron
