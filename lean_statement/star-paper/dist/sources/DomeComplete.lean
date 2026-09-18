import SixVertexUnfolding.Geometry.DomeOppositePetals
import SixVertexUnfolding.Geometry.EdgeIncidence

/-! Every convex dome unfolds by retaining its original base hinges. -/

namespace SixVertexUnfolding.ConvexPolyhedron

namespace Face

variable {P : ConvexPolyhedron}

/-- A third facet misses at least one of an original hinge's two endpoints. -/
theorem hinge_endpoints_with_one_outside (base F G : P.Face) (shared : P.ShareEdge base F)
    (G_base : G ≠ base) (G_F : G ≠ F) :
    ∃ a b : P.Vertex, a ≠ b ∧
      (a : Space) ∈ base.val ∧ (b : Space) ∈ base.val ∧
      (a : Space) ∈ F.val ∧ (b : Space) ∈ F.val ∧ (a : Space) ∉ G.val := by
  obtain ⟨a, av, b, bv, ab, edge⟩ := base.shared_edge_endpoints F shared
  have a_common : a ∈ base.val ∩ F.val := by rw [edge]; exact left_mem_segment ℝ a b
  have b_common : b ∈ base.val ∩ F.val := by rw [edge]; exact right_mem_segment ℝ a b
  by_cases aG : a ∈ G.val
  · have bG : b ∉ G.val := by
      intro member
      have contains : base.val ∩ F.val ⊆ G.val := by
        rw [edge]
        exact G.convex.segment_subset aG member
      exact (base.facets_containing_shared_edge F shared G contains).elim G_base G_F
    exact ⟨⟨b, bv⟩, ⟨a, av⟩, (fun same => ab (congrArg Subtype.val same).symm),
      b_common.1, a_common.1, b_common.2, a_common.2, bG⟩
  · exact ⟨⟨a, av⟩, ⟨b, bv⟩, (fun same => ab (congrArg Subtype.val same)),
      a_common.1, b_common.1, a_common.2, b_common.2, aG⟩

end Face

namespace Dome

variable {P : ConvexPolyhedron} {dome : P.Dome}

/-- Every pair of distinct outward petals has disjoint interior, with no bound on the number of vertices. -/
theorem Development.petals_nonoverlap (net : dome.Development) (F G : P.Face)
    (F_side : F ≠ dome.base) (G_side : G ≠ dome.base) (different : F ≠ G) :
    Disjoint (interior (net.place F '' F.val)) (interior (net.place G '' G.val)) := by
  obtain ⟨center, inside⟩ := P.solid
  obtain ⟨facets⟩ := P.exists_normalized_facets inside
  obtain ⟨a, b, ab, aB, bB, aF, bF, aG⟩ := dome.base.hinge_endpoints_with_one_outside F G
    (dome.side_shares_base F F_side) G_side different.symm
  obtain ⟨c, d, cd, cB, dB, cG, dG, cF⟩ := dome.base.hinge_endpoints_with_one_outside G F
    (dome.side_shares_base G G_side) F_side different
  exact net.opposite_petals_nonoverlap facets F G F_side G_side a b c d ab cd
    aB bB cB dB aF bF cG dG aG cF

/-- The whole-face flower of any convex dome is an original-edge unfolding. -/
theorem hasEdgeUnfolding (dome : P.Dome) : P.HasEdgeUnfolding := by
  obtain ⟨net⟩ := dome.exists_development
  exact Development.hasEdgeUnfolding dome net (fun F G hF hG hFG =>
    Development.petals_nonoverlap net F G hF hG hFG)

end Dome
end SixVertexUnfolding.ConvexPolyhedron
