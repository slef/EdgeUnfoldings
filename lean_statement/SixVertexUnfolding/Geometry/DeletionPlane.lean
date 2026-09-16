import SixVertexUnfolding.Geometry.EdgeGraph

/-! A plane through two removed vertices can also be chosen through any surviving vertex. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- At most two prescribed vertices and a chosen anchor lie in a plane with a nonzero normal. -/
theorem exists_plane_through_deleted_vertices (P : ConvexPolyhedron)
    (deleted : Finset P.Vertex) (small : deleted.card ≤ 2) (anchor : P.Vertex) :
    ∃ n : Space, n ≠ 0 ∧ ∀ w ∈ deleted, inner ℝ n w = inner ℝ n anchor := by
  classical
  let differences := deleted.image (fun w : P.Vertex => (w : Space) - (anchor : Space))
  let D := Submodule.span ℝ (differences : Set Space)
  have dimension : Module.finrank ℝ D ≤ 2 :=
    (finrank_span_finset_le_card differences).trans ((Finset.card_image_le).trans small)
  have dimensions := D.finrank_add_finrank_orthogonal
  have ambient : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [ambient] at dimensions
  have orthogonal_nonzero : Dᗮ ≠ ⊥ := by
    intro zero
    rw [zero, finrank_bot, add_zero] at dimensions
    omega
  obtain ⟨n, orthogonal, nonzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot orthogonal_nonzero
  refine ⟨n, nonzero, ?_⟩
  intro w hw
  have difference : (w : Space) - (anchor : Space) ∈ D :=
    Submodule.subset_span (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  have zero := (D.mem_orthogonal' n).mp orthogonal _ difference
  exact sub_eq_zero.mp (by simpa only [inner_sub_right] using zero)

end SixVertexUnfolding.ConvexPolyhedron
