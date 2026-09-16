import SixVertexUnfolding.Geometry.StrictSupport
import SixVertexUnfolding.Geometry.EdgeGraph

/-! Break ties in a linear height while preserving every strict vertex-height comparison. -/

namespace SixVertexUnfolding

/-- On a finite set, a sufficiently large multiple of f dominates every reversal caused by g. -/
theorem finite_height_perturbation {V : Type*} [Finite V] (f g : V → ℝ) :
    ∃ t : ℝ, 0 < t ∧ ∀ a b, f a < f b → t * f a + g a < t * f b + g b := by
  let ratios : V × V → ℝ := fun pair => (g pair.1 - g pair.2) / (f pair.2 - f pair.1)
  obtain ⟨bound, upper⟩ := (Set.finite_range ratios).bddAbove
  let t := max bound 0 + 1
  refine ⟨t, by dsimp [t]; positivity, ?_⟩
  intro a b increasing
  have ratio_lt : (g a - g b) / (f b - f a) < t :=
    (upper (Set.mem_range_self (a, b))).trans_lt (by dsimp [t]; linarith [le_max_left bound 0])
  have scaled := (div_lt_iff₀ (sub_pos.mpr increasing)).mp ratio_lt
  nlinarith

namespace ConvexPolyhedron

/-- A height can be perturbed to have a unique highest vertex without reversing strict comparisons. -/
theorem exists_height_with_unique_maximum (P : ConvexPolyhedron) (height : Space) :
    ∃ (m : Space) (top : P.Vertex),
      (∀ w : P.Vertex, w ≠ top → inner ℝ m w < inner ℝ m top) ∧
      (∀ a b : P.Vertex, inner ℝ height a < inner ℝ height b → inner ℝ m a < inner ℝ m b) := by
  classical
  have inhabited : (Finset.univ : Finset P.Vertex).Nonempty := by
    obtain ⟨v, hv⟩ := P.vertices_nonempty
    exact ⟨⟨v, hv⟩, Finset.mem_univ _⟩
  obtain ⟨top, _, maximal⟩ := Finset.univ.exists_max_image
    (fun w : P.Vertex => inner ℝ height w) inhabited
  obtain ⟨secondary, strict⟩ := P.vertex_strict_support top.property
  obtain ⟨t, _, preserves⟩ := finite_height_perturbation
    (fun w : P.Vertex => inner ℝ height w) (fun w : P.Vertex => inner ℝ secondary w)
  let m := t • height + secondary
  have value (w : P.Vertex) : inner ℝ m w = t * inner ℝ height w + inner ℝ secondary w := by
    simp [m, inner_add_left, inner_smul_left]
  refine ⟨m, top, ?_, ?_⟩
  · intro w distinct
    have upper := maximal w (Finset.mem_univ _)
    rw [value w, value top]
    rcases lt_or_eq_of_le upper with below | equal
    · exact preserves w top below
    · rw [equal]
      have secondary_lt := strict w w.property (fun same => distinct (Subtype.ext same))
      linarith
  · intro a b increasing
    simpa only [value] using preserves a b increasing

end ConvexPolyhedron
end SixVertexUnfolding
