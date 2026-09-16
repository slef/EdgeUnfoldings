import SixVertexUnfolding.Geometry.Faces

/-! Linear separators for whole polygonal faces, with boundary contact allowed. -/

namespace SixVertexUnfolding

/-- Opposite closed halfplanes have disjoint interiors. Surjectivity excludes a constant test. -/
theorem disjoint_interiors_of_halfplanes
    {A B : Set Plane} (height : Plane →L[ℝ] ℝ)
    (onto : Function.Surjective height) (level : ℝ)
    (left : ∀ x ∈ A, height x ≤ level)
    (right : ∀ x ∈ B, level ≤ height x) :
    Disjoint (interior A) (interior B) := by
  have strict_left : interior A ⊆ {x | height x < level} := by
    have inclusion : A ⊆ height ⁻¹' Set.Iic level := left
    have interior_inclusion := interior_mono inclusion
    rwa [height.interior_preimage onto, interior_Iic] at interior_inclusion
  apply Set.disjoint_left.mpr
  intro x hxA hxB
  exact (not_lt_of_ge (right x (interior_subset hxB))) (strict_left hxA)

namespace ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- An affine placement's upper bound on the original vertices holds on the whole face. -/
theorem upper_bound_of_vertices
    (place : Space →ᵃ[ℝ] Plane) (height : Plane →L[ℝ] ℝ) (level : ℝ)
    (bound : ∀ x ∈ F.val ∩ (P.vertices : Set Space), height (place x) ≤ level) :
    ∀ x ∈ F.val, height (place x) ≤ level := by
  have convex_bound : Convex ℝ {x : Space | height (place x) ≤ level} :=
    ((convex_Iic level).linear_preimage height.toLinearMap).affine_preimage place
  rw [F.eq_convexHull_vertices]
  exact convexHull_min bound convex_bound

theorem lower_bound_of_vertices
    (place : Space →ᵃ[ℝ] Plane) (height : Plane →L[ℝ] ℝ) (level : ℝ)
    (bound : ∀ x ∈ F.val ∩ (P.vertices : Set Space), level ≤ height (place x)) :
    ∀ x ∈ F.val, level ≤ height (place x) := by
  have convex_bound : Convex ℝ {x : Space | level ≤ height (place x)} :=
    ((convex_Ici level).linear_preimage height.toLinearMap).affine_preimage place
  rw [F.eq_convexHull_vertices]
  exact convexHull_min bound convex_bound

end ConvexPolyhedron.Face

/-- A finite vertex separation certificate establishes the actual public unfolding predicate.
The affine maps are only required to preserve distances on their respective faces. -/
theorem hasEdgeUnfolding_of_affine_separators
    (P : ConvexPolyhedron)
    (place : P.Face → Space →ᵃ[ℝ] Plane) (hinges : SimpleGraph P.Face)
    (tree : hinges.IsTree)
    (original_edges : ∀ F G, hinges.Adj F G → P.ShareEdge F G)
    (rigid : ∀ F, ∀ x ∈ F.val, ∀ y ∈ F.val,
      dist (place F x) (place F y) = dist x y)
    (joined : ∀ F G, hinges.Adj F G → ∀ x ∈ F.val ∩ G.val,
      place F x = place G x)
    (separators : ∀ F G, F ≠ G →
      ∃ height : Plane →L[ℝ] ℝ, Function.Surjective height ∧
      ∃ level : ℝ,
        (∀ x ∈ F.val ∩ (P.vertices : Set Space), height (place F x) ≤ level) ∧
        (∀ x ∈ G.val ∩ (P.vertices : Set Space), level ≤ height (place G x))) :
    P.HasEdgeUnfolding := by
  refine ⟨{
    place := fun F => place F
    hinges := hinges
    tree := tree
    original_edges := original_edges
    rigid := rigid
    joined := joined
    nonoverlap := ?_
  }⟩
  intro F G distinct
  obtain ⟨height, onto, level, left, right⟩ := separators F G distinct
  apply disjoint_interiors_of_halfplanes height onto level
  · rintro _ ⟨x, hx, rfl⟩
    exact F.upper_bound_of_vertices (place F) height level left x hx
  · rintro _ ⟨x, hx, rfl⟩
    exact G.lower_bound_of_vertices (place G) height level right x hx

end SixVertexUnfolding
