import SixVertexUnfolding.Geometry.SmallPolyhedra
import SixVertexUnfolding.Geometry.DualConnectivity
import SixVertexUnfolding.Geometry.VertexFacets

/-!
For a four-vertex solid, every facet consists of the other three vertices.
The opposite-vertex indexing supplies concrete faces for the tetrahedron case.
-/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Every solid convex polyhedron has at least four facets. -/
theorem four_le_facet_count (P : ConvexPolyhedron) : 4 ≤ Nat.card P.Face := by
  obtain ⟨F⟩ := P.dualGraph_connected.nonempty
  obtain ⟨v, vertex, outside⟩ := F.exists_vertex_outside
  have lower := P.three_le_incident_facet_count vertex
  have proper : {G : P.Face | v ∈ G.val} ⊂ Set.univ := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨Set.subset_univ _, ?_⟩
    intro equal
    exact outside (show F ∈ {G : P.Face | v ∈ G.val} from equal.symm ▸ Set.mem_univ F)
  have upper := Set.ncard_lt_ncard proper (Set.toFinite _)
  change 3 ≤ Nat.card ({G : P.Face | v ∈ G.val} : Set P.Face) at lower
  rw [Nat.card_coe_set_eq] at lower
  have upper' : {G : P.Face | v ∈ G.val}.ncard < Nat.card P.Face := by simpa using upper
  omega

namespace Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- Every facet of a four-vertex solid has exactly three original vertices. -/
theorem vertex_count_of_four (size : P.vertices.card = 4) :
    (F.val ∩ (P.vertices : Set Space)).ncard = 3 := by
  have lower := F.three_le_vertex_count
  have upper := F.vertex_count_lt
  omega

/-- A facet omitting v contains all three other vertices. -/
theorem vertices_eq_except_of_four (size : P.vertices.card = 4) (v : P.Vertex)
    (outside : (v : Space) ∉ F.val) :
    F.val ∩ (P.vertices : Set Space) = (P.vertices : Set Space) \ {(v : Space)} := by
  apply Set.eq_of_subset_of_ncard_le
  · intro x hx
    exact ⟨hx.2, fun equal => outside (equal ▸ hx.1)⟩
  · rw [Set.ncard_diff_singleton_of_mem v.property, Set.ncard_coe_finset,
      F.vertex_count_of_four size, size]
  · exact P.vertices.finite_toSet.diff

end Face

/-- Each vertex of a four-vertex solid has a facet consisting of precisely the other vertices. -/
theorem exists_opposite_face (P : ConvexPolyhedron) (size : P.vertices.card = 4) (v : P.Vertex) :
    ∃ F : P.Face, F.val ∩ (P.vertices : Set Space) =
      (P.vertices : Set Space) \ {(v : Space)} := by
  have omitted (F : P.Face) : ∃ w : P.Vertex, (w : Space) ∉ F.val := by
    obtain ⟨w, vertex, outside⟩ := F.exists_vertex_outside
    exact ⟨⟨w, vertex⟩, outside⟩
  choose missing excluded using omitted
  have injective : Function.Injective missing := by
    intro F G same
    apply F.eq_of_same_vertices G
    rw [F.vertices_eq_except_of_four size (missing F) (excluded F),
      G.vertices_eq_except_of_four size (missing G) (excluded G), same]
  have enough : Nat.card P.Vertex ≤ Nat.card P.Face := by
    have lower := P.four_le_facet_count
    simpa [Nat.card_eq_fintype_card, P.vertex_card, size] using lower
  obtain ⟨F, same⟩ := (injective.bijective_of_nat_card_le enough).surjective v
  exact ⟨F, F.vertices_eq_except_of_four size v (same ▸ excluded F)⟩

/-- The triangular facet opposite an original vertex in a tetrahedron. -/
noncomputable def oppositeFace (P : ConvexPolyhedron) (size : P.vertices.card = 4)
    (v : P.Vertex) : P.Face := (P.exists_opposite_face size v).choose

theorem oppositeFace_vertices (P : ConvexPolyhedron) (size : P.vertices.card = 4) (v : P.Vertex) :
    (P.oppositeFace size v).val ∩ (P.vertices : Set Space) =
      (P.vertices : Set Space) \ {(v : Space)} := (P.exists_opposite_face size v).choose_spec

theorem vertex_mem_oppositeFace (P : ConvexPolyhedron) (size : P.vertices.card = 4)
    (v w : P.Vertex) : (w : Space) ∈ (P.oppositeFace size v).val ↔ w ≠ v := by
  have membership := Set.ext_iff.mp (P.oppositeFace_vertices size v) (w : Space)
  simpa only [Set.mem_inter_iff, w.property, and_true, Set.mem_diff, true_and,
    Set.mem_singleton_iff, Subtype.val_inj] using membership

theorem oppositeFace_eq_hull (P : ConvexPolyhedron) (size : P.vertices.card = 4) (v : P.Vertex) :
    (P.oppositeFace size v).val = convexHull ℝ ((P.vertices : Set Space) \ {(v : Space)}) := by
  rw [(P.oppositeFace size v).eq_convexHull_vertices, P.oppositeFace_vertices]

/-- No facets are missing or duplicated in the opposite-vertex indexing. -/
theorem oppositeFace_bijective (P : ConvexPolyhedron) (size : P.vertices.card = 4) :
    Function.Bijective (P.oppositeFace size) := by
  constructor
  · intro v w same
    by_contra distinct
    have member := (P.vertex_mem_oppositeFace size w v).mpr distinct
    rw [← same] at member
    exact (P.vertex_mem_oppositeFace size v v).mp member rfl
  · intro F
    obtain ⟨v, vertex, outside⟩ := F.exists_vertex_outside
    let w : P.Vertex := ⟨v, vertex⟩
    refine ⟨w, (P.oppositeFace size w).eq_of_same_vertices F ?_⟩
    rw [P.oppositeFace_vertices, F.vertices_eq_except_of_four size w outside]

theorem facet_count_of_four (P : ConvexPolyhedron) (size : P.vertices.card = 4) :
    Nat.card P.Face = 4 := by
  have count := Nat.card_eq_of_bijective (P.oppositeFace size) (P.oppositeFace_bijective size)
  simpa [Nat.card_eq_fintype_card, P.vertex_card, size] using count.symm

/-- After specifying two tetrahedron vertices, exactly two original vertices remain. -/
theorem tetrahedron_remaining_pair (P : ConvexPolyhedron) (size : P.vertices.card = 4)
    (v w : P.Vertex) (distinct : v ≠ w) :
    ∃ a b : P.Vertex, a ≠ b ∧ a ≠ v ∧ a ≠ w ∧ b ≠ v ∧ b ≠ w ∧
      ∀ x : P.Vertex, (x ≠ v ∧ x ≠ w) ↔ x = a ∨ x = b := by
  have count : (Set.univ \ ({v, w} : Set P.Vertex)).ncard = 2 := by
    rw [Set.ncard_diff (Set.subset_univ _), Set.ncard_univ, Set.ncard_pair distinct]
    simp [Nat.card_eq_fintype_card, size]
  obtain ⟨a, b, ab, pair⟩ := Set.ncard_eq_two.mp count
  have a_mem : a ∈ Set.univ \ ({v, w} : Set P.Vertex) := by rw [pair]; simp
  have b_mem : b ∈ Set.univ \ ({v, w} : Set P.Vertex) := by rw [pair]; simp
  have a_out : a ≠ v ∧ a ≠ w := by simpa using a_mem
  have b_out : b ≠ v ∧ b ≠ w := by simpa using b_mem
  refine ⟨a, b, ab, a_out.1, a_out.2, b_out.1, b_out.2, ?_⟩
  intro x
  have same := Set.ext_iff.mp pair x
  simpa using same

end SixVertexUnfolding.ConvexPolyhedron
