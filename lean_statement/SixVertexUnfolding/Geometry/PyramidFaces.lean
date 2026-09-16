import SixVertexUnfolding.Geometry.FacetVertices
import SixVertexUnfolding.Geometry.Edges
import SixVertexUnfolding.Geometry.EdgeGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
A pyramid is a public polyhedron with one original vertex outside a base facet.
This proof-only description introduces neither extra faces nor a triangulation.
-/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- All original vertices except the apex belong to one whole base facet. -/
structure Pyramid (P : ConvexPolyhedron) where
  base : P.Face
  apex : P.Vertex
  apex_outside : (apex : Space) ∉ base.val
  other_vertices : ∀ v : P.Vertex, v ≠ apex → (v : Space) ∈ base.val

namespace Pyramid

variable {P : ConvexPolyhedron} (p : P.Pyramid)

/-- Every facet other than the base contains the apex. -/
theorem apex_mem_side (F : P.Face) (side : F ≠ p.base) : (p.apex : Space) ∈ F.val := by
  by_contra outside
  apply side
  apply F.eq_of_subset p.base
  rw [F.eq_convexHull_vertices]
  apply convexHull_min _ p.base.convex
  rintro x ⟨in_face, vertex⟩
  exact p.other_vertices ⟨x, vertex⟩ (fun same => outside (congrArg Subtype.val same ▸ in_face))

/-- Every side facet shares a complete original edge with the base. -/
theorem side_shares_base (F : P.Face) (side : F ≠ p.base) : P.ShareEdge F p.base := by
  have apex_in := p.apex_mem_side F side
  let common := (F.val ∩ p.base.val) ∩ (P.vertices : Set Space)
  have common_eq : common = (F.val ∩ (P.vertices : Set Space)) \ {(p.apex : Space)} := by
    ext x
    constructor
    · rintro ⟨⟨xF, xB⟩, vertex⟩
      exact ⟨⟨xF, vertex⟩, fun same => p.apex_outside (same ▸ xB)⟩
    · rintro ⟨⟨xF, vertex⟩, different⟩
      exact ⟨⟨xF, p.other_vertices ⟨x, vertex⟩
        (fun same => different (congrArg Subtype.val same))⟩, vertex⟩
  have count : 2 ≤ common.ncard := by
    rw [common_eq, Set.ncard_diff_singleton_of_mem
      (show (p.apex : Space) ∈ F.val ∩ (P.vertices : Set Space) from ⟨apex_in, p.apex.property⟩)]
    have lower := F.three_le_vertex_count
    omega
  obtain ⟨a, a_in, b, b_in, ab⟩ := (Set.one_lt_ncard
    (P.vertices.finite_toSet.subset Set.inter_subset_right : common.Finite)).mp
      (by omega : 1 < common.ncard)
  have lower := affineDimension_mono (show ({a, b} : Set Space) ⊆ F.val ∩ p.base.val from by
    rintro x (rfl | rfl)
    exacts [a_in.1, b_in.1])
  rw [affineDimension_pair ab] at lower
  have upper := F.intersection_dimension_le_one p.base side
  exact le_antisymm upper lower

/-- Every side is exactly the apex triangle on its original base edge. -/
theorem side_vertices (F : P.Face) (side : F ≠ p.base) :
    ∃ a b : P.Vertex, a ≠ b ∧
      (a : Space) ∈ p.base.val ∧ (b : Space) ∈ p.base.val ∧
      (F.val ∩ p.base.val) ∩ (P.vertices : Set Space) = {(a : Space), (b : Space)} ∧
      F.val ∩ (P.vertices : Set Space) = {(a : Space), (b : Space), (p.apex : Space)} := by
  obtain ⟨a, b, ab, common⟩ := F.shared_vertices_eq_pair p.base (p.side_shares_base F side)
  have a_in : a ∈ (F.val ∩ p.base.val) ∩ (P.vertices : Set Space) := by rw [common]; simp
  have b_in : b ∈ (F.val ∩ p.base.val) ∩ (P.vertices : Set Space) := by rw [common]; simp
  refine ⟨⟨a, a_in.2⟩, ⟨b, b_in.2⟩, fun same => ab (congrArg Subtype.val same),
    a_in.1.2, b_in.1.2, common, ?_⟩
  ext x
  constructor
  · rintro ⟨xF, vertex⟩
    by_cases at_apex : x = (p.apex : Space)
    · exact Or.inr (Or.inr at_apex)
    have in_base := p.other_vertices ⟨x, vertex⟩
      (fun same => at_apex (congrArg Subtype.val same))
    have member : x ∈ ({a, b} : Set Space) := common ▸ ⟨⟨xF, in_base⟩, vertex⟩
    exact member.elim Or.inl (fun equal => Or.inr (Or.inl equal))
  · rintro (rfl | rfl | rfl)
    exacts [⟨a_in.1.1, a_in.2⟩, ⟨b_in.1.1, b_in.2⟩, ⟨p.apex_mem_side F side, p.apex.property⟩]

/-- Retain only original hinges meeting the base, with a spanning tree among them. -/
theorem exists_face_star :
    ∃ hinges : SimpleGraph P.Face, hinges.IsTree ∧ hinges ≤ P.dualGraph ∧
      ∀ F G, hinges.Adj F G → F = p.base ∨ G = p.base := by
  let star : SimpleGraph P.Face := {
    Adj := fun F G => F ≠ G ∧ (F = p.base ∨ G = p.base)
    symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  have connected : star.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨p.base, ?_⟩
    intro F
    by_cases same : p.base = F
    · subst F
      exact SimpleGraph.Reachable.rfl
    · exact (show star.Adj p.base F from ⟨same, Or.inl rfl⟩).reachable
  obtain ⟨hinges, inside_star, tree⟩ := connected.exists_isTree_le
  refine ⟨hinges, tree, ?_, fun _ _ edge => (inside_star edge).2⟩
  intro F G edge
  obtain ⟨different, at_base⟩ := inside_star edge
  rcases at_base with rfl | rfl
  · exact G.shareEdge_symm p.base (p.side_shares_base G different.symm)
  · exact p.side_shares_base F different

end Pyramid
end SixVertexUnfolding.ConvexPolyhedron
