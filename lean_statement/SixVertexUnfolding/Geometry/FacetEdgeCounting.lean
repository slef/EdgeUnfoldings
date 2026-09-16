import SixVertexUnfolding.Geometry.QuadrilateralEdges
import SixVertexUnfolding.Geometry.TriangularFacets
import SixVertexUnfolding.Geometry.EdgeFacePairs

/-! Count the original edges of whole facets and their two-facet incidences. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- The finite set of original edges, independent of choices of finite enumerations. -/
noncomputable def originalEdges (P : ConvexPolyhedron) : Finset (Sym2 P.Vertex) :=
  P.edgeGraph.edgeSet.toFinite.toFinset

@[simp] theorem mem_originalEdges (P : ConvexPolyhedron) (e : Sym2 P.Vertex) :
    e ∈ P.originalEdges ↔ e ∈ P.edgeGraph.edgeSet := by
  simp [originalEdges]

namespace Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- The original edges whose two endpoints belong to this whole facet. -/
noncomputable def edgeFinset : Finset (Sym2 P.Vertex) := by
  classical
  exact P.originalEdges.filter (fun e => ∀ v ∈ e, (v : Space) ∈ F.val)

@[simp] theorem mem_edgeFinset (a b : P.Vertex) :
    s(a, b) ∈ F.edgeFinset ↔ P.edgeGraph.Adj a b ∧ (a : Space) ∈ F.val ∧ (b : Space) ∈ F.val := by
  classical
  simp only [edgeFinset, Finset.mem_filter, mem_originalEdges, SimpleGraph.mem_edgeSet]
  constructor
  · rintro ⟨edge, contains⟩
    exact ⟨edge, contains a (by simp), contains b (by simp)⟩
  · rintro ⟨edge, aF, bF⟩
    refine ⟨edge, ?_⟩
    intro v member
    rcases Sym2.mem_iff.mp member with rfl | rfl
    exacts [aF, bF]

/-- A triangular facet has precisely its three endpoint pairs as original edges. -/
theorem triangle_edgeFinset (a b c : P.Vertex) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (vertices : F.val ∩ (P.vertices : Set Space) = {(a : Space), (b : Space), (c : Space)}) :
    F.edgeFinset = {s(a, b), s(a, c), s(b, c)} := by
  classical
  have member (v : P.Vertex) : (v : Space) ∈ F.val ↔ v = a ∨ v = b ∨ v = c := by
    constructor
    · intro on_face
      have belongs := vertices ▸ (show (v : Space) ∈ F.val ∩ (P.vertices : Set Space) from
        ⟨on_face, v.property⟩)
      rcases belongs with va | vb | vc
      exacts [Or.inl (Subtype.ext va), Or.inr (Or.inl (Subtype.ext vb)), Or.inr (Or.inr (Subtype.ext vc))]
    · intro same
      have belongs : (v : Space) ∈ F.val ∩ (P.vertices : Set Space) := by
        rw [vertices]
        rcases same with rfl | rfl | rfl <;> simp
      exact belongs.1
  have edge_ab := F.triangle_vertices_adjacent a b c ab ac bc vertices
  have edge_ac := F.triangle_vertices_adjacent a c b ac ab bc.symm (by
    rw [vertices]; ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
  have edge_bc := F.triangle_vertices_adjacent b c a bc ab.symm ac.symm (by
    rw [vertices]; ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
  ext e
  induction e using Sym2.inductionOn with
  | hf x y =>
    simp only [F.mem_edgeFinset, member, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨edge, (rfl | rfl | rfl), (rfl | rfl | rfl)⟩
      all_goals first | exact False.elim (edge.ne rfl) | simp [Sym2.eq_swap]
    · intro pair
      rcases pair with pair | pair | pair
      all_goals
        rcases Sym2.eq_iff.mp pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        all_goals refine ⟨?_, by simp, by simp⟩
        all_goals first | assumption | exact edge_ab.symm | exact edge_ac.symm | exact edge_bc.symm

/-- A triangular facet has three original edges. -/
theorem triangle_edge_count (triangle : (F.val ∩ (P.vertices : Set Space)).ncard = 3) :
    F.edgeFinset.card = 3 := by
  classical
  obtain ⟨a, b, c, ab, ac, bc, vertices⟩ := Set.ncard_eq_three.mp triangle
  have vertex (x : Space) (member : x ∈ ({a, b, c} : Set Space)) : x ∈ P.vertices :=
    (vertices ▸ member).2
  let A : P.Vertex := ⟨a, vertex a (Or.inl rfl)⟩
  let B : P.Vertex := ⟨b, vertex b (Or.inr (Or.inl rfl))⟩
  let C : P.Vertex := ⟨c, vertex c (Or.inr (Or.inr rfl))⟩
  have AB : A ≠ B := fun same => ab (congrArg Subtype.val same)
  have AC : A ≠ C := fun same => ac (congrArg Subtype.val same)
  have BC : B ≠ C := fun same => bc (congrArg Subtype.val same)
  rw [F.triangle_edgeFinset A B C AB AC BC vertices]
  simp [AB, AC, BC, Ne.symm AB, Ne.symm BC]

namespace Quadrilateral

variable {F} (Q : F.Quadrilateral)

/-- The four consecutive endpoint pairs are distinct. -/
theorem side_injective : Function.Injective (fun i : Fin 4 => s(Q.corner i, Q.corner (i + 1))) := by
  intro i j same
  rcases Sym2.eq_iff.mp same with ⟨first, _⟩ | ⟨first, second⟩
  · exact Q.distinct first
  · have first_index := Q.distinct first
    have second_index := Q.distinct second
    have no_two_cycle : ∀ i j : Fin 4, i = j + 1 → i + 1 = j → False := by decide
    exact False.elim (no_two_cycle i j first_index second_index)

/-- The quadrilateral's original edges are exactly its four consecutive endpoint pairs. -/
theorem edgeFinset_eq_sides :
    F.edgeFinset = Finset.univ.image (fun i : Fin 4 => s(Q.corner i, Q.corner (i + 1))) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf a b =>
    constructor
    · intro member
      obtain ⟨edge, aF, bF⟩ := F.mem_edgeFinset a b |>.mp member
      obtain ⟨i, ai⟩ := Q.vertices ▸ (show (a : Space) ∈ F.val ∩ (P.vertices : Set Space) from ⟨aF, a.property⟩)
      obtain ⟨j, bj⟩ := Q.vertices ▸ (show (b : Space) ∈ F.val ∩ (P.vertices : Set Space) from ⟨bF, b.property⟩)
      have ai : Q.corner i = a := Subtype.ext ai
      have bj : Q.corner j = b := Subtype.ext bj
      rw [← ai, ← bj] at edge ⊢
      rcases (Q.adjacent_iff_consecutive i j).mp edge with rfl | rfl
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, Sym2.eq_swap⟩
    · intro member
      obtain ⟨i, _, pair⟩ := Finset.mem_image.mp member
      rw [← pair]
      exact F.mem_edgeFinset _ _ |>.mpr
        ⟨Q.consecutive_adjacent i, Q.corner_mem i, Q.corner_mem (i + 1)⟩

end Quadrilateral

/-- A quadrilateral facet has four original edges. -/
theorem quadrilateral_edge_count (four : (F.val ∩ (P.vertices : Set Space)).ncard = 4) :
    F.edgeFinset.card = 4 := by
  classical
  obtain ⟨Q⟩ := F.exists_quadrilateral four
  rw [Q.edgeFinset_eq_sides, Finset.card_image_of_injective _ Q.side_injective]
  simp

end Face

/-- Every original edge appears on exactly two facets, also when edges carry arbitrary natural weights. -/
theorem weighted_facet_edge_count (P : ConvexPolyhedron) [Fintype P.Face] (weight : Sym2 P.Vertex → ℕ) :
    ∑ F : P.Face, ∑ e ∈ F.edgeFinset, weight e =
      2 * ∑ e ∈ P.originalEdges, weight e := by
  classical
  have twice (e : Sym2 P.Vertex) (edge : e ∈ P.originalEdges) :
      (∑ F : P.Face, if (∀ v ∈ e, (v : Space) ∈ F.val) then weight e else 0) = 2 * weight e := by
    induction e using Sym2.inductionOn with
    | hf a b =>
      have adjacent : P.edgeGraph.Adj a b := by
        simpa only [P.mem_originalEdges, SimpleGraph.mem_edgeSet] using edge
      obtain ⟨F, G, different, aF, bF, aG, bG, only_two⟩ := P.edge_incident_faces a b adjacent
      have incident (H : P.Face) : (∀ v ∈ s(a, b), (v : Space) ∈ H.val) ↔ H = F ∨ H = G := by
        constructor
        · exact fun member => only_two H (member a (by simp)) (member b (by simp))
        · rintro (rfl | rfl)
          · intro v member
            rcases Sym2.mem_iff.mp member with rfl | rfl
            exacts [aF, bF]
          · intro v member
            rcases Sym2.mem_iff.mp member with rfl | rfl
            exacts [aG, bG]
      simp_rw [incident]
      have filter_eq : Finset.univ.filter (fun H : P.Face => H = F ∨ H = G) = {F, G} := by
        ext H
        simp
      rw [← Finset.sum_filter, filter_eq]
      simp [different, two_mul]
  simp only [Face.edgeFinset, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    _ = ∑ e ∈ P.originalEdges, 2 * weight e := Finset.sum_congr rfl twice
    _ = _ := (Finset.mul_sum _ _ _).symm

end SixVertexUnfolding.ConvexPolyhedron
