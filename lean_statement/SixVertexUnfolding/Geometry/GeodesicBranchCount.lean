import SixVertexUnfolding.Geometry.UniqueGeodesicNeighborhoods

/-! Near a target inside one face, the number of normalized shortest routes
cannot exceed its value at that target. No branch can appear away from the
old routes or split into two nearby routes. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- With the source fixed, nearby targets have no more shortest routes than the given unique-face target. -/
theorem geodesic_count_nearby (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    ∃ V : Set (frontier P.body), IsOpen V ∧ b ∈ V ∧
      ∀ c ∈ V, Nat.card (P.geodesicFiber a c) ≤ Nat.card (P.geodesicFiber a b) := by
  classical
  let J := P.geodesicFiber a b
  letI : Fintype J := (graph.geodesicFiber_finite small_faces a b different).fintype
  have neighborhoods (f : J) : ∃ W : Set P.BoundaryCurve, IsOpen W ∧ f.val ∈ W ∧
      ∀ g ∈ W, ∀ h ∈ W, g ∈ P.geodesicCurves → h ∈ P.geodesicCurves →
        g 0 = f.val 0 → h 0 = f.val 0 → g 1 = h 1 → g = h := by
    have first : f.val 0 = a := congrArg Prod.fst f.property.2
    have last : f.val 1 = b := congrArg Prod.snd f.property.2
    exact graph.geodesic_branch_isolation small_faces f.val
      (by simpa only [first, last] using different) F (by simpa only [last] using unique_face)
  choose W openW memberW isolated using neighborhoods
  have covers : ∀ f ∈ P.geodesicCurves, P.curveEndpoints f = (a, b) → f ∈ ⋃ i : J, W i := by
    intro f geodesic ends
    exact mem_iUnion.mpr ⟨⟨f, geodesic, ends⟩, memberW ⟨f, geodesic, ends⟩⟩
  obtain ⟨N, openN, abN, near⟩ := P.geodesic_family_upper_continuous (a, b) (⋃ i : J, W i)
    (isOpen_iUnion openW) covers
  refine ⟨(fun c => (a, c)) ⁻¹' N, openN.preimage (continuous_const.prodMk continuous_id), abN, ?_⟩
  intro c cN
  have covered (g : P.geodesicFiber a c) : ∃ i : J, g.val ∈ W i :=
    mem_iUnion.mp (near g.val g.property.1 (g.property.2 ▸ cN))
  choose index member using covered
  apply Nat.card_le_card_of_injective index
  intro g h equal
  apply Subtype.ext
  have same_branch : h.val ∈ W (index g) := by rw [equal]; exact member h
  exact isolated (index g) g.val (member g) h.val same_branch g.property.1 h.property.1
    ((congrArg Prod.fst g.property.2).trans (congrArg Prod.fst (index g).property.2).symm)
    ((congrArg Prod.fst h.property.2).trans (congrArg Prod.fst (index g).property.2).symm)
    ((congrArg Prod.snd g.property.2).trans (congrArg Prod.snd h.property.2).symm)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
