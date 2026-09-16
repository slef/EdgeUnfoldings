import SixVertexUnfolding.Geometry.TwoRouteNeighborhoods
import SixVertexUnfolding.Geometry.SmallPolyhedronRouteStability

/-! Around a regular two-route target, each old route has its own
neighborhood containing exactly one route to every nearby two-route target.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- The two actual routes persist separately wherever the nearby route count remains two. -/
theorem small_two_route_neighborhoods (a b : frontier P.body) (different : a ≠ b)
    (not_vertex : (b : Space) ∉ P.vertices) (two : Nat.card (P.geodesicFiber a b) = 2) :
    ∃ V : Set (frontier P.body), IsOpen V ∧ b ∈ V ∧
      ∃ U W : Set P.BoundaryCurve, IsOpen U ∧ IsOpen W ∧ Disjoint U W ∧
        ∀ c ∈ V, Nat.card (P.geodesicFiber a c) = 2 →
          ∃ f ∈ P.geodesicFiber a c ∩ U, ∃ g ∈ P.geodesicFiber a c ∩ W,
            f ≠ g ∧ P.geodesicFiber a c = {f, g} := by
  obtain ⟨f, g, fg, pair⟩ := ncard_eq_two.mp two
  have f_mem : f ∈ P.geodesicFiber a b := by rw [pair]; simp
  have g_mem : g ∈ P.geodesicFiber a b := by rw [pair]; simp
  have f0 : f 0 = a := congrArg Prod.fst f_mem.2
  have f1 : f 1 = b := congrArg Prod.snd f_mem.2
  have g0 : g 0 = a := congrArg Prod.fst g_mem.2
  have g1 : g 1 = b := congrArg Prod.snd g_mem.2
  obtain ⟨U₀, openU₀, fU₀, isolate_f⟩ := small_geodesic_branch_isolation_nonvertex size small_faces f
    (by simpa only [f0, f1] using different) (by simpa only [f1] using not_vertex)
  obtain ⟨W₀, openW₀, gW₀, isolate_g⟩ := small_geodesic_branch_isolation_nonvertex size small_faces g
    (by simpa only [g0, g1] using different) (by simpa only [g1] using not_vertex)
  obtain ⟨A, B, openA, openB, fA, gB, apart⟩ := t2_separation fg
  let U := U₀ ∩ A
  let W := W₀ ∩ B
  have openU : IsOpen U := openU₀.inter openA
  have openW : IsOpen W := openW₀.inter openB
  have disjoint : Disjoint U W := apart.mono inter_subset_right inter_subset_right
  obtain ⟨N, openN, abN, near⟩ := P.geodesic_family_upper_continuous (a, b) (U ∪ W)
    (openU.union openW) (by
      intro h geodesic ends
      have member : h ∈ P.geodesicFiber a b := ⟨geodesic, ends⟩
      rw [pair] at member
      rcases member with rfl | rfl
      · exact Or.inl ⟨fU₀, fA⟩
      · exact Or.inr ⟨gW₀, gB⟩)
  refine ⟨(fun c => (a, c)) ⁻¹' N, openN.preimage (continuous_const.prodMk continuous_id),
    abN, U, W, openU, openW, disjoint, ?_⟩
  intro c hc count
  apply two_point_split (P.geodesicFiber a c) U W count
    (fun h hh => near h hh.1 (hh.2 ▸ hc)) disjoint
  · intro h hh k hk
    exact isolate_f h hh.2.1 k hk.2.1 hh.1.1 hk.1.1
      ((congrArg Prod.fst hh.1.2).trans f0.symm) ((congrArg Prod.fst hk.1.2).trans f0.symm)
      ((congrArg Prod.snd hh.1.2).trans (congrArg Prod.snd hk.1.2).symm)
  · intro h hh k hk
    exact isolate_g h hh.2.1 k hk.2.1 hh.1.1 hk.1.1
      ((congrArg Prod.fst hh.1.2).trans g0.symm) ((congrArg Prod.fst hk.1.2).trans g0.symm)
      ((congrArg Prod.snd hh.1.2).trans (congrArg Prod.snd hk.1.2).symm)

end SixVertexUnfolding.ConvexPolyhedron
