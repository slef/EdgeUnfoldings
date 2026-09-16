import SixVertexUnfolding.Geometry.UniversalVertexFanCoverage
import SixVertexUnfolding.Geometry.FacetEdgeCounting
import SixVertexUnfolding.Geometry.VertexFacets

/-! The face-angle count needed for a six-vertex universal source.
Five triangular faces meet the source. At least two more faces exclude it;
edge double-counting rules out a total angle weight smaller than eight.
No global Euler formula or prescribed graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Distinct original vertices can be separated by an incident facet. -/
theorem exists_incident_facet_excluding (P : ConvexPolyhedron) (v w : P.Vertex)
    (different : v ≠ w) : ∃ F : P.Face, (v : Space) ∈ F.val ∧ (w : Space) ∉ F.val := by
  by_contra no_face
  push Not at no_face
  obtain ⟨normal, level, _, face_eq, body_eq⟩ := P.exists_facet_halfspace_representation
  have spanning := P.incident_normals_span normal level face_eq body_eq v.property
  have vanishes : Set.EqOn (innerSL ℝ ((w : Space) - v)).toLinearMap
      (0 : Space →ₗ[ℝ] ℝ) (normal '' {F | (v : Space) ∈ F.val}) := by
    rintro _ ⟨F, vF, rfl⟩
    have at_v : inner ℝ (normal F) v = level F := by
      have belongs : (v : Space) ∈ F.val := vF
      rw [face_eq F] at belongs
      exact belongs.2
    have at_w : inner ℝ (normal F) w = level F := by
      have belongs := no_face F vF
      rw [face_eq F] at belongs
      exact belongs.2
    change inner ℝ ((w : Space) - v) (normal F) = 0
    rw [real_inner_comm, inner_sub_right, at_w, at_v, sub_self]
  have everywhere := LinearMap.eqOn_span vanishes
  rw [spanning] at everywhere
  have zero := everywhere (show (w : Space) - v ∈ (⊤ : Submodule ℝ Space) from trivial)
  change inner ℝ ((w : Space) - v) ((w : Space) - v) = 0 at zero
  exact different (Subtype.ext (sub_eq_zero.mp (inner_self_eq_zero.mp zero)).symm)

variable {P : ConvexPolyhedron} (size : P.vertices.card = 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Two different original facets exclude any specified vertex in this small-face family. -/
theorem two_facets_excluding_vertex (source : P.Vertex) :
    ∃ F G : P.Face, F ≠ G ∧ (source : Space) ∉ F.val ∧ (source : Space) ∉ G.val := by
  classical
  obtain ⟨v, vertex, different⟩ := P.vertices.exists_mem_ne (by omega) (source : Space)
  obtain ⟨F, _, outside⟩ := P.exists_incident_facet_excluding ⟨v, vertex⟩ source
    (fun equal => different (congrArg Subtype.val equal))
  by_contra only_one
  have unique (G : P.Face) (not_source : (source : Space) ∉ G.val) : G = F := by
    by_contra distinct
    exact only_one ⟨F, G, (fun same => distinct same.symm), outside, not_source⟩
  have covers : (P.vertices : Set Space) \ {(source : Space)} ⊆ F.val ∩ (P.vertices : Set Space) := by
    rintro x ⟨original, not_source⟩
    obtain ⟨G, on_face, excluded⟩ := P.exists_incident_facet_excluding ⟨x, original⟩ source
      (fun equal => not_source (congrArg Subtype.val equal))
    exact ⟨unique G excluded ▸ on_face, original⟩
  have count := Set.ncard_le_ncard covers (P.vertices.finite_toSet.subset inter_subset_right)
  have source_mem : {(source : Space)} ⊆ (P.vertices : Set Space) := singleton_subset_iff.mpr source.property
  rw [Set.ncard_diff source_mem, Set.ncard_singleton, Set.ncard_coe_finset, size] at count
  rcases small_faces F with triangle | quadrilateral <;> omega

include size small_faces in
/-- A universal source forces at least seven original facets. -/
theorem universal_vertex_seven_le_face_count [Fintype P.Face]
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v) :
    7 ≤ Fintype.card P.Face := by
  classical
  have incident := P.universal_vertex_incident_face_count size small_faces source universal
  obtain ⟨F, G, different, first, second⟩ := two_facets_excluding_vertex size small_faces source
  have two : 2 ≤ Fintype.card {H : P.Face // (source : Space) ∉ H.val} := by
    have pair : ({⟨F, first⟩, ⟨G, second⟩} : Finset {H : P.Face // (source : Space) ∉ H.val}).card = 2 := by
      simp [show (⟨F, first⟩ : {H : P.Face // (source : Space) ∉ H.val}) ≠ ⟨G, second⟩ from
        fun equal => different (congrArg Subtype.val equal)]
    exact pair ▸ Finset.card_le_univ _
  have partition := Fintype.card_subtype_compl (fun H : P.Face => (source : Space) ∈ H.val)
  rw [Nat.card_eq_fintype_card] at incident
  omega

include size small_faces in
/-- The sum of the triangular/quadrilateral face-angle weights is at least eight. -/
theorem universal_vertex_face_angle_weight [Fintype P.Face]
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v) :
    8 ≤ ∑ F : P.Face, ((F.val ∩ (P.vertices : Set Space)).ncard - 2) := by
  classical
  let triangular (F : P.Face) := (F.val ∩ (P.vertices : Set Space)).ncard = 3
  let t := (Finset.univ.filter triangular).card
  let q := (Finset.univ.filter (fun F => ¬ triangular F)).card
  have partition : t + q = Fintype.card P.Face := by
    simpa only [t, q, Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) triangular
  have faces : 7 ≤ t + q := partition ▸ universal_vertex_seven_le_face_count size small_faces source universal
  have incident := P.universal_vertex_incident_face_count size small_faces source universal
  have injection : Function.Injective
      (fun F : {F : P.Face // (source : Space) ∈ F.val} =>
        (⟨F.val, P.universal_vertex_facets_triangular small_faces source universal F.val F.property⟩ :
          {F : P.Face // triangular F})) := by
    intro F G same
    apply Subtype.ext
    exact congrArg (fun H : {H : P.Face // triangular H} => H.val) same
  have triangles : 5 ≤ t := by
    have bound := Fintype.card_le_of_injective _ injection
    rw [← Nat.card_eq_fintype_card] at bound
    rw [incident] at bound
    simpa only [Fintype.card_subtype, t] using bound
  have edge_weight : (∑ F : P.Face, F.edgeFinset.card) = 3 * t + 4 * q := by
    have each (F : P.Face) : F.edgeFinset.card = if triangular F then 3 else 4 := by
      rcases small_faces F with three | four
      · rw [if_pos three, F.triangle_edge_count three]
      · rw [if_neg (by dsimp [triangular]; omega), F.quadrilateral_edge_count four]
    simp_rw [each]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, smul_eq_mul]
    change t * 3 + q * 4 = 3 * t + 4 * q
    omega
  have double_count : (∑ F : P.Face, F.edgeFinset.card) = 2 * P.originalEdges.card := by
    simpa using P.weighted_facet_edge_count (fun _ => 1)
  rw [edge_weight] at double_count
  have weight : (∑ F : P.Face, ((F.val ∩ (P.vertices : Set Space)).ncard - 2)) = t + 2 * q := by
    have each (F : P.Face) : (F.val ∩ (P.vertices : Set Space)).ncard - 2 =
        if triangular F then 1 else 2 := by
      rcases small_faces F with three | four
      · rw [if_pos three, three]
      · rw [if_neg (by dsimp [triangular]; omega), four]
    simp_rw [each]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    change t + q * 2 = t + 2 * q
    omega
  rw [weight]
  omega

end SixVertexUnfolding.ConvexPolyhedron
