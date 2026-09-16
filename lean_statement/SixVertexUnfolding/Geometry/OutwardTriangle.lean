import SixVertexUnfolding.Geometry.HingeSides
import SixVertexUnfolding.Geometry.VoronoiSeparation
import SixVertexUnfolding.Geometry.FacePlacement

/-! Place a neighboring triangle on the outward side and separate it from the base triangle. -/

namespace SixVertexUnfolding

/-- Two triangles on opposite sides of their common edge have disjoint interiors. -/
theorem opposite_triangles_disjoint (a b x y : Plane)
    (noncollinear : ¬ Collinear ℝ ({a, b, x} : Set Plane))
    (opposite : OppositeHingeSides a b x y) :
    Disjoint (interior (convexHull ℝ ({a, b, x} : Set Plane)))
      (interior (convexHull ℝ ({a, b, y} : Set Plane))) := by
  have distinct : a ≠ b := by
    intro same
    apply noncollinear
    simpa [same] using collinear_pair ℝ b x
  let n := hingeSideVector a b x
  have n_nonzero : n ≠ 0 := hingeSideVector_ne_zero a b x noncollinear
  have b_zero : inner ℝ n (b - a) = 0 := by
    rw [hingeSideVector_inner a b x b distinct, hingeSideVector_right a b distinct, inner_zero_right]
  have x_nonnegative : 0 ≤ inner ℝ n (x - a) := by
    rw [hingeSideVector_inner a b x x distinct]
    exact real_inner_self_nonneg
  have y_nonpositive : inner ℝ n (y - a) ≤ 0 := by
    rw [hingeSideVector_inner a b x y distinct]
    exact opposite
  have base_bound : ∀ z ∈ convexHull ℝ ({a, b, x} : Set Plane), inner ℝ n a ≤ inner ℝ n z := by
    apply convexHull_min _ (convex_halfSpace_ge
      ⟨fun u v => inner_add_right n u v, fun r u => inner_smul_right n u r⟩ (inner ℝ n a))
    rintro z (rfl | rfl | rfl)
    · change inner ℝ n z ≤ inner ℝ n z
      exact le_rfl
    · exact sub_nonneg.mp (by simpa only [inner_sub_right] using b_zero.ge)
    · exact sub_nonneg.mp (by simpa only [inner_sub_right] using x_nonnegative)
  have petal_bound : ∀ z ∈ convexHull ℝ ({a, b, y} : Set Plane), inner ℝ n z ≤ inner ℝ n a := by
    apply convexHull_min _ (convex_halfSpace_le
      ⟨fun u v => inner_add_right n u v, fun r u => inner_smul_right n u r⟩ (inner ℝ n a))
    rintro z (rfl | rfl | rfl)
    · change inner ℝ n z ≤ inner ℝ n z
      exact le_rfl
    · exact sub_nonpos.mp (by simpa only [inner_sub_right] using b_zero.le)
    · exact sub_nonpos.mp (by simpa only [inner_sub_right] using y_nonpositive)
  exact (disjoint_interiors_of_halfplanes (innerSL ℝ n) (plane_inner_height_surjective n_nonzero)
    (inner ℝ n a) petal_bound base_bound).symm

namespace ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- Align an original face along two given endpoints, choosing its free vertex's outward side. -/
theorem exists_outward_placement (a b x y : Space) (a_in : a ∈ F.val) (b_in : b ∈ F.val)
    (left : Space →ᵃ[ℝ] Plane) (length : dist (left a) (left b) = dist a b)
    (distinct : left a ≠ left b) :
    ∃ right : Space →ᵃ[ℝ] Plane,
      (∀ u ∈ F.val, ∀ v ∈ F.val, dist (right u) (right v) = dist u v) ∧
      right a = left a ∧ right b = left b ∧
      OppositeHingeSides (left a) (left b) (left x) (right y) := by
  obtain ⟨initial, rigid⟩ := F.exists_rigid_placement
  obtain ⟨align, at_a, at_b⟩ := exists_plane_motion (initial a) (initial b) (left a) (left b)
    ((rigid a a_in b b_in).trans length.symm)
  obtain ⟨turn, fixed_a, fixed_b, outward⟩ := exists_opposite_hinge_motion
    (left a) (left b) (left x) (align (initial y)) distinct
  let right := turn.toAffineEquiv.toAffineMap.comp (align.toAffineEquiv.toAffineMap.comp initial)
  refine ⟨right, ?_, ?_, ?_, outward⟩
  · intro u hu v hv
    change dist (turn (align (initial u))) (turn (align (initial v))) = dist u v
    rw [turn.dist_map, align.dist_map]
    exact rigid u hu v hv
  · change turn (align (initial a)) = left a
    rw [at_a, fixed_a]
  · change turn (align (initial b)) = left b
    rw [at_b, fixed_b]

end ConvexPolyhedron.Face
end SixVertexUnfolding
