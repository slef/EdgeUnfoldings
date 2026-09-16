import SixVertexUnfolding.Geometry.PolygonPetal

/-! A face-star development of a dome, with whole facets and all base-petal comparisons proved. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- A dome has one original base facet adjacent to every other facet. -/
structure Dome (P : ConvexPolyhedron) where
  base : P.Face
  side_shares_base : ∀ F : P.Face, F ≠ base → P.ShareEdge base F

namespace Dome

variable {P : ConvexPolyhedron} (dome : P.Dome)

/-- The original hinges around the base contain a tree on all whole facets. -/
theorem exists_face_star :
    ∃ hinges : SimpleGraph P.Face, hinges.IsTree ∧ hinges ≤ P.dualGraph ∧
      ∀ F G, hinges.Adj F G → F = dome.base ∨ G = dome.base := by
  let star : SimpleGraph P.Face := {
    Adj := fun F G => F ≠ G ∧ (F = dome.base ∨ G = dome.base)
    symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  have connected : star.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨dome.base, ?_⟩
    intro F
    by_cases same : dome.base = F
    · subst F
      exact SimpleGraph.Reachable.rfl
    · exact (show star.Adj dome.base F from ⟨same, Or.inl rfl⟩).reachable
  obtain ⟨hinges, inside_star, tree⟩ := connected.exists_isTree_le
  refine ⟨hinges, tree, ?_, fun _ _ edge => (inside_star edge).2⟩
  intro F G edge
  obtain ⟨different, at_base⟩ := inside_star edge
  rcases at_base with rfl | rfl
  · exact dome.side_shares_base G different.symm
  · exact dome.base.shareEdge_symm F (dome.side_shares_base F different)

/-- Intermediate construction: the base is separated from every attached whole facet. -/
structure Development where
  place : P.Face → Space →ᵃ[ℝ] Plane
  rigid : ∀ F, ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place F x) (place F y) = dist x y
  joined : ∀ F, Set.EqOn (place dome.base) (place F) (dome.base.val ∩ F.val)
  base_safe : ∀ F, F ≠ dome.base →
    Disjoint (interior (place dome.base '' dome.base.val)) (interior (place F '' F.val))
  farther : ∀ F, F ≠ dome.base → ∀ x y : P.Vertex,
    (x : Space) ∈ dome.base.val → (x : Space) ∉ F.val →
    (y : Space) ∈ F.val → (y : Space) ∉ dome.base.val →
    dist (x : Space) y < dist (place dome.base x) (place F y)
  outward : ∀ F, F ≠ dome.base →
    ∀ a ∈ (dome.base.val ∩ F.val) ∩ (P.vertices : Set Space),
    ∀ b ∈ (dome.base.val ∩ F.val) ∩ (P.vertices : Set Space), a ≠ b →
    ∀ x ∈ dome.base.val, ∀ y ∈ F.val,
      OppositeHingeSides (place dome.base a) (place dome.base b) (place dome.base x) (place F y)

/-- Construct all outward polygonal attachments with no assumptions about their mutual separation. -/
theorem exists_development : Nonempty dome.Development := by
  classical
  obtain ⟨base_place, base_rigid⟩ := dome.base.exists_rigid_placement
  have attachments (F : {F : P.Face // F ≠ dome.base}) :=
    dome.base.exists_polygon_petal F.val (dome.side_shares_base F.val F.property) base_place base_rigid
  choose side rigid joined base_safe farther outward using attachments
  let place (F : P.Face) : Space →ᵃ[ℝ] Plane :=
    if h : F = dome.base then base_place else side ⟨F, h⟩
  have at_base : place dome.base = base_place := by simp [place]
  have at_side (F : P.Face) (h : F ≠ dome.base) : place F = side ⟨F, h⟩ := by simp [place, h]
  refine ⟨⟨place, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro F
    by_cases h : F = dome.base
    · subst F
      rw [at_base]
      exact base_rigid
    · rw [at_side F h]
      exact rigid ⟨F, h⟩
  · intro F
    by_cases h : F = dome.base
    · subst F
      exact fun _ _ => rfl
    · rw [at_base, at_side F h]
      exact joined ⟨F, h⟩
  · intro F h
    rw [at_base, at_side F h]
    exact base_safe ⟨F, h⟩
  · intro F h
    rw [at_base, at_side F h]
    exact farther ⟨F, h⟩
  · intro F h
    rw [at_base, at_side F h]
    exact outward ⟨F, h⟩

/-- After the remaining petal-pair comparisons, the development is a public original-edge unfolding. -/
theorem Development.hasEdgeUnfolding (net : dome.Development)
    (petals_safe : ∀ F G : P.Face, F ≠ dome.base → G ≠ dome.base → F ≠ G →
      Disjoint (interior (net.place F '' F.val)) (interior (net.place G '' G.val))) :
    P.HasEdgeUnfolding := by
  obtain ⟨hinges, tree, original, star⟩ := dome.exists_face_star
  refine ⟨⟨fun F => net.place F, hinges, tree, fun _ _ edge => original edge, net.rigid, ?_, ?_⟩⟩
  · intro F G edge x hx
    rcases star F G edge with rfl | rfl
    · exact net.joined G hx
    · exact (net.joined F ⟨hx.2, hx.1⟩).symm
  · intro F G different
    by_cases fbase : F = dome.base
    · subst F
      exact net.base_safe G different.symm
    by_cases gbase : G = dome.base
    · subst G
      exact (net.base_safe F different).symm
    exact petals_safe F G fbase gbase different

end Dome
end SixVertexUnfolding.ConvexPolyhedron
