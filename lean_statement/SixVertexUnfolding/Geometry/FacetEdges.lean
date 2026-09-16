import SixVertexUnfolding.Geometry.HeightPerturbation
import SixVertexUnfolding.Geometry.HingeCoordinates

/-!
An edge exposed inside an original facet is also an original edge of the solid.
In particular, all three sides of an original triangular facet are original edges.
-/

namespace SixVertexUnfolding

/-- A nondegenerate triangle has a linear height maximized precisely along a chosen side. -/
theorem triangle_edge_height (a b c : Space)
    (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Space)) :
    ∃ q : Space, inner ℝ q a = inner ℝ q b ∧ inner ℝ q c < inner ℝ q a := by
  have ab : a ≠ b := by
    intro same
    apply noncollinear
    simpa [same] using collinear_pair ℝ b c
  let axis := NormedSpace.normalize (b - a)
  let perpendicular := hingeRemainder axis (c - a)
  have unit : ‖axis‖ = 1 := NormedSpace.norm_normalize (sub_ne_zero.mpr ab.symm)
  have nonzero : perpendicular ≠ 0 := by
    intro zero
    have same : c - a = inner ℝ axis (c - a) • axis := sub_eq_zero.mp zero
    apply noncollinear
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨a, b - a, ?_⟩
    intro x hx
    rcases hx with hx | hx | hx
    · exact ⟨0, by simp [hx]⟩
    · exact ⟨1, by simp [hx]⟩
    · rw [hx]
      refine ⟨inner ℝ axis (c - a) * ‖b - a‖⁻¹, ?_⟩
      dsimp [axis, NormedSpace.normalize] at same
      rw [smul_smul] at same
      simpa using eq_add_of_sub_eq same
  have orthogonal : inner ℝ perpendicular axis = 0 := by
    simpa only [real_inner_comm] using hingeRemainder_orthogonal unit (c - a)
  have edge_zero : inner ℝ perpendicular (b - a) = 0 := by
    rw [← NormedSpace.norm_smul_normalize (b - a), inner_smul_right]
    change ‖b - a‖ * inner ℝ perpendicular axis = 0
    rw [orthogonal, mul_zero]
  have height : inner ℝ perpendicular (c - a) = ‖perpendicular‖ ^ 2 := by
    have self := real_inner_self_eq_norm_sq perpendicular
    change inner ℝ perpendicular (c - a - inner ℝ axis (c - a) • axis) = _ at self
    simpa only [inner_sub_right, inner_smul_right, orthogonal, mul_zero, sub_zero] using self
  refine ⟨-perpendicular, ?_, ?_⟩
  · simp only [inner_neg_left, inner_sub_right] at edge_zero ⊢
    linarith
  · simp only [inner_neg_left]
    have positive := sq_pos_of_pos (norm_pos_iff.mpr nonzero)
    rw [inner_sub_right] at height
    linarith

namespace ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- A height exposing two vertices within a facet certifies their original edge in the solid. -/
theorem edge_of_exposing_height (a b : P.Vertex) (ab : a ≠ b)
    (aF : (a : Space) ∈ F.val) (bF : (b : Space) ∈ F.val) (q : Space)
    (equal_height : inner ℝ q a = inner ℝ q b)
    (strict : ∀ v : P.Vertex, (v : Space) ∈ F.val → v ≠ a → v ≠ b →
      inner ℝ q v < inner ℝ q a) : P.edgeGraph.Adj a b := by
  classical
  obtain ⟨_, n, level, _, support, face_eq⟩ := F.property
  have a_height := (face_eq ▸ aF).2
  have b_height := (face_eq ▸ bF).2
  obtain ⟨t, _, preserves⟩ := finite_height_perturbation
    (fun v : P.Vertex => inner ℝ n v) (fun v : P.Vertex => inner ℝ q v)
  let m := t • n + q
  have value (v : P.Vertex) : inner ℝ m v = t * inner ℝ n v + inner ℝ q v := by
    simp only [m, inner_add_left, real_inner_smul_left]
  have tied : inner ℝ m a = inner ℝ m b := by rw [value, value, a_height, b_height, equal_height]
  have lower (v : P.Vertex) (va : v ≠ a) (vb : v ≠ b) : inner ℝ m v < inner ℝ m a := by
    rw [value, value]
    by_cases vF : (v : Space) ∈ F.val
    · have v_height : inner ℝ n v = level := (face_eq ▸ vF).2
      rw [v_height, a_height]
      linarith [strict v vF va vb]
    · apply preserves v a
      rw [a_height]
      apply lt_of_le_of_ne (support v (P.vertices_subset_body v.property))
      intro equal
      exact vF (face_eq ▸ ⟨P.vertices_subset_body v.property, equal⟩)
  have contacts : (P.contactVertices m a : Set Space) = {(a : Space), (b : Space)} := by
    ext x
    simp only [contactVertices, Finset.mem_coe, Finset.mem_filter, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨vertex, height⟩
      by_contra neither
      push Not at neither
      exact (lower ⟨x, vertex⟩ (fun same => neither.1 (congrArg Subtype.val same))
        (fun same => neither.2 (congrArg Subtype.val same))).ne height
    · rintro (rfl | rfl)
      exacts [⟨a.property, rfl⟩, ⟨b.property, tied.symm⟩]
  apply P.edgeGraph_adj_of_contact_pair a b ab m (P.normal_ne_zero_of_contact_pair a b ab m contacts)
    _ contacts
  apply P.supportsAt_of_vertex_bounds
  intro x vertex
  let v : P.Vertex := ⟨x, vertex⟩
  by_cases va : v = a
  · exact le_of_eq (congrArg (fun w : P.Vertex => inner ℝ m w) va)
  by_cases vb : v = b
  · exact le_of_eq ((congrArg (fun w : P.Vertex => inner ℝ m w) vb).trans tied.symm)
  exact (lower v va vb).le

/-- Each side of an original triangular facet is an original edge. -/
theorem triangle_vertices_adjacent (a b c : P.Vertex) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (vertices : F.val ∩ (P.vertices : Set Space) = {(a : Space), (b : Space), (c : Space)}) :
    P.edgeGraph.Adj a b := by
  have aF : (a : Space) ∈ F.val := by
    have : (a : Space) ∈ F.val ∩ (P.vertices : Set Space) := by rw [vertices]; simp
    exact this.1
  have bF : (b : Space) ∈ F.val := by
    have : (b : Space) ∈ F.val ∩ (P.vertices : Set Space) := by rw [vertices]; simp
    exact this.1
  obtain ⟨q, tied, lower⟩ := triangle_edge_height a b c
    (P.no_three_collinear_vertices a.property b.property c.property
      (fun same => ab (Subtype.ext same)) (fun same => ac (Subtype.ext same))
      (fun same => bc (Subtype.ext same)))
  apply F.edge_of_exposing_height a b ab aF bF q tied
  intro v vF va vb
  have member : (v : Space) ∈ ({(a : Space), (b : Space), (c : Space)} : Set Space) :=
    vertices ▸ ⟨vF, v.property⟩
  rcases member with same | same | same
  · exact False.elim (va (Subtype.ext same))
  · exact False.elim (vb (Subtype.ext same))
  · change inner ℝ q (v : Space) < inner ℝ q (a : Space)
    rw [same]
    exact lower

/-- Any two different original vertices of a triangular facet are adjacent. -/
theorem adjacent_of_triangle (triangle : (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (a b : P.Vertex) (ab : a ≠ b) (aF : (a : Space) ∈ F.val) (bF : (b : Space) ∈ F.val) :
    P.edgeGraph.Adj a b := by
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
  let third : P.Vertex := ⟨c, c_in.1.2⟩
  apply F.triangle_vertices_adjacent a b third ab
    (fun same => c_in.2 (Or.inl (congrArg Subtype.val same).symm))
    (fun same => c_in.2 (Or.inr (congrArg Subtype.val same).symm))
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

end ConvexPolyhedron.Face
end SixVertexUnfolding
