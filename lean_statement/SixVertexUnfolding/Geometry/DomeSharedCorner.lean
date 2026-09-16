import SixVertexUnfolding.Geometry.DomeDevelopment
import SixVertexUnfolding.Geometry.FacetSupportingCorner
import SixVertexUnfolding.Geometry.MetricCornerCones

/-! Two dome petals meeting at a trihedral base corner cannot overlap. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Dome.Development

variable {P : ConvexPolyhedron} {dome : P.Dome} (net : dome.Development)

/-- Whole polygonal petals are separated at a shared original base corner. -/
theorem shared_corner_nonoverlap (F G : P.Face) (F_side : F ≠ dome.base) (G_side : G ≠ dome.base)
    (o a b d : P.Vertex) (oa : o ≠ a) (ob : o ≠ b)
    (oB : (o : Space) ∈ dome.base.val) (aB : (a : Space) ∈ dome.base.val) (bB : (b : Space) ∈ dome.base.val)
    (oF : (o : Space) ∈ F.val) (aF : (a : Space) ∈ F.val) (dF : (d : Space) ∈ F.val)
    (oG : (o : Space) ∈ G.val) (bG : (b : Space) ∈ G.val) (dG : (d : Space) ∈ G.val)
    (dB : (d : Space) ∉ dome.base.val) (aG : (a : Space) ∉ G.val) (bF : (b : Space) ∉ F.val) :
    Disjoint (interior (net.place F '' F.val)) (interior (net.place G '' G.val)) := by
  have oa' : (o : Space) ≠ (a : Space) := fun same => oa (Subtype.ext same)
  have ob' : (o : Space) ≠ (b : Space) := fun same => ob (Subtype.ext same)
  have od : (o : Space) ≠ (d : Space) := fun same => dB (same ▸ oB)
  have ad : (a : Space) ≠ (d : Space) := fun same => dB (same ▸ aB)
  have bd : (b : Space) ≠ (d : Space) := fun same => dB (same ▸ bB)
  have ab : (a : Space) ≠ (b : Space) := fun same => aG (same.symm ▸ bG)
  have base_triangle := P.no_three_collinear_vertices o.property a.property b.property oa' ob' ab
  have left_triangle := P.no_three_collinear_vertices o.property a.property d.property oa' od ad
  have right_triangle := P.no_three_collinear_vertices o.property b.property d.property ob' od bd
  have spatial : (d : Space) ∉ affineSpan ℝ ({(o : Space), (a : Space), (b : Space)} : Set Space) := by
    intro member
    apply dome.base.outside_affineSpan (P.vertices_subset_body d.property) dB
    apply affineSpan_mono ℝ (show ({(o : Space), (a : Space), (b : Space)} : Set Space) ⊆ dome.base.val from ?_) member
    rintro x (rfl | rfl | rfl)
    exacts [oB, aB, bB]
  have joined_oF := net.joined F ⟨oB, oF⟩
  have joined_aF := net.joined F ⟨aB, aF⟩
  have joined_oG := net.joined G ⟨oB, oG⟩
  have joined_bG := net.joined G ⟨bB, bG⟩
  have left_cone := F.placed_in_supporting_corner dome.base G (net.place F) o a d
    oF aF dF oB aB dB oG dG aG left_triangle
  have right_cone := G.placed_in_supporting_corner dome.base F (net.place G) o b d
    oG bG dG oB bB dB oF dF bF right_triangle
  rw [← joined_oF, ← joined_aF] at left_cone
  rw [← joined_oG, ← joined_bG] at right_cone
  apply Disjoint.mono (interior_mono left_cone) (interior_mono right_cone)
  apply outward_trihedral_cones_disjoint o a b d
    (net.place dome.base o) (net.place dome.base a) (net.place dome.base b)
    (net.place F d) (net.place G d) oa' ob' base_triangle spatial
    (net.rigid dome.base o oB a aB) (net.rigid dome.base o oB b bB) (net.rigid dome.base a aB b bB)
  · rw [joined_oF]
    exact net.rigid F o oF d dF
  · rw [joined_aF]
    exact net.rigid F a aF d dF
  · rw [joined_oG]
    exact net.rigid G o oG d dG
  · rw [joined_bG]
    exact net.rigid G b bG d dG
  · exact net.outward F F_side o ⟨⟨oB, oF⟩, o.property⟩ a ⟨⟨aB, aF⟩, a.property⟩ oa' b bB d dF
  · exact net.outward G G_side o ⟨⟨oB, oG⟩, o.property⟩ b ⟨⟨bB, bG⟩, b.property⟩ ob' a aB d dG

end SixVertexUnfolding.ConvexPolyhedron.Dome.Development
