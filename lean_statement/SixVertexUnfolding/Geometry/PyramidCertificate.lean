import SixVertexUnfolding.Geometry.PyramidFaces
import SixVertexUnfolding.Geometry.VertexCertificate
import SixVertexUnfolding.Geometry.VoronoiSeparation

/-!
The pyramid flower keeps the base whole. Each side has its own copy of the apex.
Distance comparisons at base vertices separate every pair of side triangles.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.Pyramid

/-- Strictly farther apex copies at missing base vertices certify the whole flower. -/
theorem unfolding_of_copies {P : ConvexPolyhedron} (p : P.Pyramid)
    (copy : P.Face → Space →ᵃ[ℝ] Plane)
    (rigid : ∀ F, ∀ x ∈ F.val, ∀ y ∈ F.val, dist (copy F x) (copy F y) = dist x y)
    (joined : ∀ F, ∀ x : P.Vertex, (x : Space) ∈ F.val → (x : Space) ∈ p.base.val →
      copy F x = copy p.base x)
    (base_safe : ∀ F, F ≠ p.base →
      Disjoint (interior (copy p.base '' p.base.val)) (interior (copy F '' F.val)))
    (farther : ∀ F, F ≠ p.base → ∀ x : P.Vertex, (x : Space) ∈ p.base.val →
      (x : Space) ∉ F.val → dist (x : Space) p.apex < dist (copy p.base x) (copy F p.apex)) :
    P.HasEdgeUnfolding := by
  obtain ⟨hinges, tree, original, star⟩ := p.exists_face_star
  refine ⟨{
    place := fun F => copy F
    hinges := hinges
    tree := tree
    original_edges := fun _ _ edge => original edge
    rigid := rigid
    joined := ?_
    nonoverlap := ?_
  }⟩
  · intro F G edge
    apply F.joined_of_vertex_agreement G (copy F) (copy G)
    rintro x ⟨⟨xF, xG⟩, vertex⟩
    rcases star F G edge with rfl | rfl
    · exact (joined G ⟨x, vertex⟩ xG xF).symm
    · exact joined F ⟨x, vertex⟩ xF xG
  · intro F G different
    by_cases F_base : F = p.base
    · subst F
      exact base_safe G different.symm
    by_cases G_base : G = p.base
    · subst G
      exact (base_safe F F_base).symm
    have apexF := p.apex_mem_side F F_base
    have apexG := p.apex_mem_side G G_base
    have missing : ∃ x : P.Vertex, (x : Space) ∈ F.val ∧ (x : Space) ∉ G.val := by
      by_contra none
      push Not at none
      apply different
      apply F.eq_of_subset G
      rw [F.eq_convexHull_vertices]
      apply convexHull_min _ G.convex
      rintro x ⟨xF, vertex⟩
      exact none ⟨x, vertex⟩ xF
    obtain ⟨v, vF, vG⟩ := missing
    have v_base := p.other_vertices v (fun same => vG (same ▸ apexG))
    have sites_distinct : copy F p.apex ≠ copy G p.apex := by
      intro same
      have distance := rigid F v vF p.apex apexF
      rw [joined F v vF v_base, same] at distance
      exact (farther G G_base v v_base vG).ne distance.symm
    have nearer (I J : P.Face) (I_side : I ≠ p.base) (J_side : J ≠ p.base)
        (x : Space) (hx : x ∈ I.val ∩ (P.vertices : Set Space)) :
        dist (copy I x) (copy I p.apex) ≤ dist (copy I x) (copy J p.apex) := by
      let v : P.Vertex := ⟨x, hx.2⟩
      by_cases at_apex : v = p.apex
      · have equal : x = (p.apex : Space) := congrArg Subtype.val at_apex
        simp [equal]
      have v_base := p.other_vertices v at_apex
      rw [rigid I x hx.1 p.apex (p.apex_mem_side I I_side)]
      change dist (v : Space) p.apex ≤ dist (copy I v) (copy J p.apex)
      rw [joined I v hx.1 v_base]
      by_cases vJ : (v : Space) ∈ J.val
      · have distance := rigid J v vJ p.apex (p.apex_mem_side J J_side)
        rw [joined J v vJ v_base] at distance
        exact distance.ge
      · exact (farther J J_side v v_base vJ).le
    exact F.disjoint_of_nearer_sites G (copy F) (copy G) (copy F p.apex) (copy G p.apex)
      sites_distinct (nearer F G F_base G_base) (nearer G F G_base F_base)

end SixVertexUnfolding.ConvexPolyhedron.Pyramid
