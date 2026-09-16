import SixVertexUnfolding.Geometry.FacetEdges

/-! Extract the three actual vertices of an original triangular facet. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- Two distinct vertices on a triangular facet determine its third original vertex. -/
theorem exists_third_vertex (triangle : (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (a b : P.Vertex) (ab : a ≠ b) (aF : (a : Space) ∈ F.val) (bF : (b : Space) ∈ F.val) :
    ∃ c : P.Vertex, c ≠ a ∧ c ≠ b ∧
      F.val ∩ (P.vertices : Set Space) = {(a : Space), (b : Space), (c : Space)} := by
  have distinct : (a : Space) ≠ (b : Space) := fun same => ab (Subtype.ext same)
  have pair_subset : ({(a : Space), (b : Space)} : Set Space) ⊆ F.val ∩ (P.vertices : Set Space) := by
    rintro x (rfl | rfl)
    exacts [⟨aF, a.property⟩, ⟨bF, b.property⟩]
  have one : ((F.val ∩ (P.vertices : Set Space)) \ {(a : Space), (b : Space)}).ncard = 1 := by
    rw [Set.ncard_diff pair_subset, triangle, Set.ncard_pair distinct]
  obtain ⟨c, remaining⟩ := Set.ncard_eq_one.mp one
  have c_in : c ∈ (F.val ∩ (P.vertices : Set Space)) \ {(a : Space), (b : Space)} := by
    rw [remaining]
    rfl
  refine ⟨⟨c, c_in.1.2⟩, fun same => c_in.2 (Or.inl (congrArg Subtype.val same)),
    fun same => c_in.2 (Or.inr (congrArg Subtype.val same)), ?_⟩
  ext x
  constructor
  · intro hx
    by_cases xa : x = (a : Space)
    · exact Or.inl xa
    by_cases xb : x = (b : Space)
    · exact Or.inr (Or.inl xb)
    have xc : x ∈ ({c} : Set Space) := remaining ▸ ⟨hx, by simpa using And.intro xa xb⟩
    exact Or.inr (Or.inr xc)
  · rintro (rfl | rfl | rfl)
    exacts [⟨aF, a.property⟩, ⟨bF, b.property⟩, c_in.1]

end SixVertexUnfolding.ConvexPolyhedron.Face
