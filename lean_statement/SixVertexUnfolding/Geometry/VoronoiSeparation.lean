import SixVertexUnfolding.Geometry.Separation

/-!
Two copies of an unfolded source supply a perpendicular-bisector separator.
Checking which copy is nearer at face vertices suffices for whole-face nonoverlap.
-/

namespace SixVertexUnfolding

/-- Distance comparison with two sites is a linear halfplane inequality. -/
theorem nearer_site_iff_halfplane (x p q : Plane) :
    dist x p ≤ dist x q ↔
      inner ℝ (q - p) x ≤ (‖q‖ ^ 2 - ‖p‖ ^ 2) / 2 := by
  have at_p := norm_sub_sq_real x p
  have at_q := norm_sub_sq_real x q
  have difference : inner ℝ (q - p) x = inner ℝ x q - inner ℝ x p := by
    rw [inner_sub_left]
    simp only [real_inner_comm]
  rw [difference]
  rw [dist_eq_norm, dist_eq_norm]
  constructor
  · intro nearer
    have squared := (sq_le_sq₀ (norm_nonneg (x - p)) (norm_nonneg (x - q))).mpr nearer
    linarith
  · intro bound
    apply (sq_le_sq₀ (norm_nonneg (x - p)) (norm_nonneg (x - q))).mp
    linarith

/-- A nonzero planar normal gives a surjective linear height. -/
theorem plane_inner_height_surjective {n : Plane} (nonzero : n ≠ 0) :
    Function.Surjective (innerSL ℝ n) := by
  intro r
  refine ⟨(r / inner ℝ n n) • n, ?_⟩
  change inner ℝ n ((r / inner ℝ n n) • n) = r
  rw [inner_smul_right]
  exact div_mul_cancel₀ r (inner_self_ne_zero.mpr nonzero)

/-- Sets lying in opposite nearest-site regions have disjoint interiors. -/
theorem disjoint_interiors_of_nearer_sites {A B : Set Plane} (p q : Plane) (distinct : p ≠ q)
    (left : ∀ x ∈ A, dist x p ≤ dist x q)
    (right : ∀ x ∈ B, dist x q ≤ dist x p) :
    Disjoint (interior A) (interior B) := by
  apply disjoint_interiors_of_halfplanes (innerSL ℝ (q - p))
    (plane_inner_height_surjective (sub_ne_zero.mpr distinct.symm))
    ((‖q‖ ^ 2 - ‖p‖ ^ 2) / 2)
  · intro x hx
    exact (nearer_site_iff_halfplane x p q).mp (left x hx)
  · intro x hx
    have bound := (nearer_site_iff_halfplane x q p).mp (right x hx)
    change (‖q‖ ^ 2 - ‖p‖ ^ 2) / 2 ≤ inner ℝ (q - p) x
    simp only [inner_sub_left] at bound ⊢
    linarith

namespace ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F G : P.Face)

/-- Vertex distance comparisons against two source copies separate the entire placed facets. -/
theorem disjoint_of_nearer_sites (left right : Space →ᵃ[ℝ] Plane)
    (p q : Plane) (distinct : p ≠ q)
    (left_nearer : ∀ x ∈ F.val ∩ (P.vertices : Set Space),
      dist (left x) p ≤ dist (left x) q)
    (right_nearer : ∀ x ∈ G.val ∩ (P.vertices : Set Space),
      dist (right x) q ≤ dist (right x) p) :
    Disjoint (interior (left '' F.val)) (interior (right '' G.val)) := by
  apply disjoint_interiors_of_nearer_sites p q distinct
  · rintro _ ⟨x, hx, rfl⟩
    apply (nearer_site_iff_halfplane _ p q).mpr
    exact F.upper_bound_of_vertices left (innerSL ℝ (q - p)) ((‖q‖ ^ 2 - ‖p‖ ^ 2) / 2)
      (fun y hy => (nearer_site_iff_halfplane _ p q).mp (left_nearer y hy)) x hx
  · rintro _ ⟨x, hx, rfl⟩
    apply (nearer_site_iff_halfplane _ q p).mpr
    exact G.upper_bound_of_vertices right (innerSL ℝ (p - q)) ((‖p‖ ^ 2 - ‖q‖ ^ 2) / 2)
      (fun y hy => (nearer_site_iff_halfplane _ q p).mp (right_nearer y hy)) x hx

end ConvexPolyhedron.Face
end SixVertexUnfolding
