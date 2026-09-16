import SixVertexUnfolding.Definitions

/-! Nonoverlap of closed triangle pieces implies nonoverlap of the whole original faces. -/

namespace SixVertexUnfolding

/-- Reassembling pieces with dense interiors cannot create a new interior overlap. -/
theorem disjoint_interiors_of_piece_covers {ι κ : Type*} (left right : Set Plane)
    (left_piece : ι → Set Plane) (right_piece : κ → Set Plane)
    (left_cover : left ⊆ ⋃ i, left_piece i) (right_cover : right ⊆ ⋃ j, right_piece j)
    (left_regular : ∀ i, closure (interior (left_piece i)) = left_piece i)
    (right_regular : ∀ j, closure (interior (right_piece j)) = right_piece j)
    (safe : ∀ i j, Disjoint (interior (left_piece i)) (interior (right_piece j))) :
    Disjoint (interior left) (interior right) := by
  have left_misses_piece (j : κ) : Disjoint left (interior (right_piece j)) := by
    apply Set.disjoint_left.mpr
    intro x xl xr
    obtain ⟨i, xi⟩ := Set.mem_iUnion.mp (left_cover xl)
    have misses := (safe i j).closure_left isOpen_interior
    rw [left_regular i] at misses
    exact Set.disjoint_left.mp misses xi xr
  have inside_misses_piece (j : κ) : Disjoint (interior left) (right_piece j) := by
    have misses := (left_misses_piece j).mono_left interior_subset
    have closed_misses := misses.closure_right isOpen_interior
    rwa [right_regular j] at closed_misses
  apply Set.disjoint_left.mpr
  intro x xl xr
  obtain ⟨j, xj⟩ := Set.mem_iUnion.mp (right_cover (interior_subset xr))
  exact Set.disjoint_left.mp (inside_misses_piece j) xl xj

/-- Two diagonal triangles on either side suffice to check two whole quadrilateral faces. -/
theorem disjoint_interiors_of_two_triangle_covers (left right : Set Plane)
    (left_piece right_piece : Fin 2 → Set Plane)
    (left_cover : left = left_piece 0 ∪ left_piece 1)
    (right_cover : right = right_piece 0 ∪ right_piece 1)
    (left_regular : ∀ i, closure (interior (left_piece i)) = left_piece i)
    (right_regular : ∀ j, closure (interior (right_piece j)) = right_piece j)
    (safe : ∀ i j, Disjoint (interior (left_piece i)) (interior (right_piece j))) :
    Disjoint (interior left) (interior right) := by
  apply disjoint_interiors_of_piece_covers left right left_piece right_piece _ _ left_regular right_regular safe
  · rw [left_cover]
    rintro x (first | second)
    exacts [Set.mem_iUnion.mpr ⟨0, first⟩, Set.mem_iUnion.mpr ⟨1, second⟩]
  · rw [right_cover]
    rintro x (first | second)
    exacts [Set.mem_iUnion.mpr ⟨0, first⟩, Set.mem_iUnion.mpr ⟨1, second⟩]

end SixVertexUnfolding
