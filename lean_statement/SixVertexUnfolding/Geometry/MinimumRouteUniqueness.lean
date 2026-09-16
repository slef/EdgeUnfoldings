import SixVertexUnfolding.Geometry.LocalSourceComparison
import SixVertexUnfolding.Geometry.SingleSourceRouteUniqueness
import SixVertexUnfolding.Geometry.ContinuousFiniteChoice

/-! In any verified finite local minimum formula, the route is unique
exactly when the source copy attaining the minimum is unique. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- A finite minimum formula detects route uniqueness without treating unused source copies as admissible. -/
theorem unique_route_iff_unique_minimum (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (bF : (b : Space) ∈ F.val) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F)
    (sources : Set Plane) (finite : sources.Finite)
    (V : Set Space) (openV : IsOpen V) (bV : (b : Space) ∈ V)
    (minimum : ∀ x ∈ V ∩ F.val,
      (∀ source ∈ sources, P.surfaceDist a x ≤ dist source (P.faceCoordinates F x)) ∧
      ∃ source ∈ sources, P.surfaceDist a x = dist source (P.faceCoordinates F x)) :
    (P.geodesicFiber a b).Subsingleton ↔
      {source ∈ sources | dist source (P.faceCoordinates F b) = P.surfaceDist a b}.Subsingleton := by
  classical
  constructor
  · intro unique
    obtain ⟨actual, _, U, openU, bU, formula⟩ :=
      graph.unique_route_source_distance small_faces a b different F unique_face unique
    have identifies (source : Plane) (member : source ∈ sources)
        (attains : dist source (P.faceCoordinates F b) = P.surfaceDist a b) : actual = source := by
      apply P.local_face_source_comparison_eq F b bF unique_face actual source (U ∩ V)
        (openU.inter openV) ⟨bU, bV⟩
      · intro x hx
        rw [← formula x ⟨hx.1.1, F.subset_frontier hx.2⟩]
        exact (minimum x ⟨hx.1.2, hx.2⟩).1 source member
      · rw [← formula b ⟨bU, b.property⟩, attains]
    intro p hp q hq
    exact (identifies p hp.1 hp.2).symm.trans (identifies q hq.1 hq.2)
  · intro unique
    letI : Fintype sources := finite.fintype
    obtain ⟨p, member, at_b⟩ := (minimum b ⟨bV, bF⟩).2
    let S := V ∩ F.val
    let formulas (q : sources) (x : Space) := dist q.val (P.faceCoordinates F x)
    have selected (x : Space) (hx : x ∈ S) : ∃ q : sources, P.surfaceDist a x = formulas q x := by
      obtain ⟨q, hq, equal⟩ := (minimum x hx).2
      exact ⟨⟨q, hq⟩, equal⟩
    have separated (q : sources) (distinct : q ≠ ⟨p, member⟩) : formulas ⟨p, member⟩ b ≠ formulas q b := by
      intro equal
      apply distinct
      apply Subtype.ext
      exact unique ⟨q.property, equal.symm.trans at_b.symm⟩ ⟨member, at_b.symm⟩
    obtain ⟨W, openW, bW, formula⟩ := continuous_finite_choice_local S (P.surfaceDist a) formulas
      ((P.surfaceDist_continuousOn a.property).mono (fun _ hx => F.subset_frontier hx.2))
      (fun q => (continuous_const.dist (P.faceCoordinates F).continuous_of_finiteDimensional).continuousOn)
      selected b ⟨bV, bF⟩ ⟨p, member⟩ at_b separated
    obtain ⟨O, openO, bO, face⟩ := P.unique_face_neighborhood F unique_face
    apply graph.unique_route_of_local_source_formula small_faces a b different F unique_face p
      ((W ∩ V) ∩ O) ((openW.inter openV).inter openO) ⟨⟨bW, bV⟩, bO⟩
    intro x hx
    exact formula x ⟨hx.1.1.1, hx.1.1.2, (face _ ⟨hx.1.2, hx.2⟩).1⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
