import SixVertexUnfolding.Geometry.EdgeBranchIsolation
import SixVertexUnfolding.Geometry.MultipleRouteTopology

/-! Route-count stability and closedness of the multiple-route locus now
hold throughout the nonvertex boundary, across original edges as well as faces. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Nearby targets have no more shortest routes than a given nonvertex target. -/
theorem geodesic_count_nearby_nonvertex (a b : frontier P.body) (different : a ≠ b)
    (not_vertex : (b : Space) ∉ P.vertices) :
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
    exact graph.geodesic_branch_isolation_nonvertex small_faces f.val
      (by simpa only [first, last] using different) (by simpa only [last] using not_vertex)
  choose W openW memberW isolated using neighborhoods
  obtain ⟨N, openN, abN, near⟩ := P.geodesic_family_upper_continuous (a, b) (⋃ i : J, W i)
    (isOpen_iUnion openW) (fun f hf ends => mem_iUnion.mpr ⟨⟨f, hf, ends⟩, memberW ⟨f, hf, ends⟩⟩)
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

include graph small_faces in
/-- Unique shortest routes remain unique near every distinct nonvertex target. -/
theorem unique_geodesics_nearby_nonvertex (a b : frontier P.body) (different : a ≠ b)
    (not_vertex : (b : Space) ∉ P.vertices) (unique_route : (P.geodesicFiber a b).Subsingleton) :
    ∃ V : Set (frontier P.body), IsOpen V ∧ b ∈ V ∧ ∀ c ∈ V, (P.geodesicFiber a c).Subsingleton := by
  obtain ⟨f, hf⟩ := P.geodesicFiber_nonempty a b
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  obtain ⟨W, openW, fW, isolated⟩ := graph.geodesic_branch_isolation_nonvertex small_faces f
    (by simpa only [first, last] using different) (by simpa only [last] using not_vertex)
  obtain ⟨N, openN, abN, contains⟩ := P.geodesic_family_upper_continuous (a, b) W openW
    (fun g geodesic ends => unique_route ⟨geodesic, ends⟩ hf ▸ fW)
  refine ⟨(fun c => (a, c)) ⁻¹' N, openN.preimage (continuous_const.prodMk continuous_id), abN, ?_⟩
  intro c cN g hg h hh
  exact isolated g (contains g hg.1 (hg.2 ▸ cN)) h (contains h hh.1 (hh.2 ▸ cN)) hg.1 hh.1
    ((congrArg Prod.fst hg.2).trans first.symm) ((congrArg Prod.fst hh.2).trans first.symm)
    ((congrArg Prod.snd hg.2).trans (congrArg Prod.snd hh.2).symm)

include graph small_faces in
/-- A limit of multiple-route targets is still multiple away from original vertices and the source. -/
theorem multiple_routes_closed_nonvertex (a b : frontier P.body) (different : a ≠ b)
    (not_vertex : (b : Space) ∉ P.vertices)
    (limit : b ∈ closure {c : frontier P.body | (c : Space) ∈ P.multipleRouteLocus a}) :
    (b : Space) ∈ P.multipleRouteLocus a := by
  rw [P.multiple_routes_iff_fiber a b]
  refine ⟨different, ?_⟩
  intro unique
  obtain ⟨V, openV, bV, unique_near⟩ := graph.unique_geodesics_nearby_nonvertex small_faces a b different not_vertex unique
  obtain ⟨c, cV, multiple⟩ := mem_closure_iff.mp limit V openV bV
  exact ((P.multiple_routes_iff_fiber a c).mp multiple).2 (unique_near c cV)

include graph small_faces in
/-- Taking closure adds no nonvertex target distinct from the source. -/
theorem closure_multiple_routes_iff_nonvertex (a b : frontier P.body) (different : a ≠ b)
    (not_vertex : (b : Space) ∉ P.vertices) :
    b ∈ closure {c : frontier P.body | (c : Space) ∈ P.multipleRouteLocus a} ↔
      (b : Space) ∈ P.multipleRouteLocus a :=
  ⟨graph.multiple_routes_closed_nonvertex small_faces a b different not_vertex,
    fun member => subset_closure (show b ∈ {c : frontier P.body | (c : Space) ∈ P.multipleRouteLocus a} from member)⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
