import SixVertexUnfolding.Geometry.BipyramidCap
import SixVertexUnfolding.Geometry.BipyramidTree
import SixVertexUnfolding.Geometry.VertexCertificate

/-!
Develop both caps about a chosen equator source. This module proves the same-cap
and central-base comparisons. BipyramidNonoverlap proves the cross-cap comparisons.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices

variable {P : ConvexPolyhedron} (B : BipyramidVertices P)

/-- Two nonoverlapping caps joined along their common original base edge. -/
structure Development
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (source : Fin 3) where
  cap : ∀ upper : Bool, B.CapPlacement triangles upper source
  bases_joined : ∀ x ∈ (B.face triangles true source).val ∩ (B.face triangles false source).val,
    (cap true).place source x = (cap false).place source x
  bases_safe :
    Disjoint (interior ((cap true).place source '' (B.face triangles true source).val))
      (interior ((cap false).place source '' (B.face triangles false source).val))
  poles_farther : dist (B.top : Space) (B.bottom : Space) <
    dist ((cap true).place source B.top) ((cap false).place source B.bottom)

/-- A development with seven of the fifteen distinct face pairs separated always exists. -/
theorem exists_development
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3) (source : Fin 3) :
    Nonempty (B.Development triangles source) := by
  let topBase := B.face triangles true source
  let bottomBase := B.face triangles false source
  obtain ⟨left, left_rigid⟩ := topBase.exists_rigid_placement
  obtain ⟨i, j, different, pair⟩ := equator_complement_pair source
  have im : i ≠ source := (Set.ext_iff.mp pair i).mpr (Or.inl rfl)
  have jm : j ≠ source := (Set.ext_iff.mp pair j).mpr (Or.inr rfl)
  have bottom_vertices : bottomBase.val ∩ (P.vertices : Set Space) =
      {(B.equatorVertex i : Space), (B.equatorVertex j : Space), (B.bottom : Space)} := by
    rw [B.face_vertices, faceVertices, pair, Set.image_insert_eq, Set.image_singleton]
    ext x
    simp only [poleVertex, Bool.false_eq_true, ↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  obtain ⟨right, right_rigid, joined, safe, farther⟩ := topBase.exists_triangle_petal bottomBase
    (B.equatorVertex i) (B.equatorVertex j) B.bottom
    (fun same => different (B.equator_injective same))
    ((B.equator_mem_face triangles true source i).mpr im)
    ((B.equator_mem_face triangles true source j).mpr jm) bottom_vertices
    (B.opposite_pole_not_mem_face triangles true source) left left_rigid
  obtain ⟨topCap, top_fixed⟩ := B.exists_cap_placement triangles true source left left_rigid
  obtain ⟨bottomCap, bottom_fixed⟩ := B.exists_cap_placement triangles false source right right_rigid
  refine ⟨{
    cap := fun upper => match upper with | true => topCap | false => bottomCap
    bases_joined := ?_
    bases_safe := ?_
    poles_farther := ?_
  }⟩
  · change ∀ x ∈ topBase.val ∩ bottomBase.val, topCap.place source x = bottomCap.place source x
    rw [top_fixed, bottom_fixed]
    apply topBase.joined_of_vertex_agreement bottomBase left right
    rintro x ⟨⟨xT, xB⟩, vertex⟩
    exact (joined ⟨x, vertex⟩ xB xT).symm
  · change Disjoint (interior (topCap.place source '' topBase.val))
      (interior (bottomCap.place source '' bottomBase.val))
    rw [top_fixed, bottom_fixed]
    exact safe
  · change dist (B.top : Space) (B.bottom : Space) <
      dist (topCap.place source B.top) (bottomCap.place source B.bottom)
    rw [top_fixed, bottom_fixed]
    exact farther B.top (B.pole_mem_face triangles true source)
      (B.opposite_pole_not_mem_face triangles false source)

namespace Development

variable {B} {triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3}
    {source : Fin 3} (net : B.Development triangles source)

/-- Assemble the public unfolding once the eight other cross-cap comparisons are supplied. -/
theorem hasEdgeUnfolding_of_cross_pairs
    (cross_safe : ∀ i j : Fin 3, i ≠ source ∨ j ≠ source →
      Disjoint (interior ((net.cap true).place i '' (B.face triangles true i).val))
        (interior ((net.cap false).place j '' (B.face triangles false j).val))) :
    P.HasEdgeUnfolding := by
  let index := B.faceEquiv triangles
  let place (F : P.Face) := (net.cap (index.symm F).1).place (index.symm F).2
  have placed (upper : Bool) (i : Fin 3) : place (B.face triangles upper i) = (net.cap upper).place i := by
    change (net.cap (index.symm (index (upper, i))).1).place (index.symm (index (upper, i))).2 = _
    rw [index.symm_apply_apply]
  obtain ⟨hinges, tree, original, star⟩ := B.exists_star_hinge_tree triangles source
  have all_cross (i j : Fin 3) :
      Disjoint (interior ((net.cap true).place i '' (B.face triangles true i).val))
        (interior ((net.cap false).place j '' (B.face triangles false j).val)) := by
    by_cases iB : i = source
    · by_cases jB : j = source
      · subst i
        subst j
        exact net.bases_safe
      · exact cross_safe i j (Or.inr jB)
    · exact cross_safe i j (Or.inl iB)
  refine ⟨{
    place := fun F => place F
    hinges := hinges
    tree := tree
    original_edges := fun _ _ edge => original edge
    rigid := ?_
    joined := ?_
    nonoverlap := ?_
  }⟩
  · intro F
    obtain ⟨⟨upper, i⟩, rfl⟩ := B.face_index_surjective triangles F
    simpa only [placed] using (net.cap upper).rigid i
  · intro F G edge
    have indexed := star F G edge
    obtain ⟨⟨upper, i⟩, rfl⟩ := B.face_index_surjective triangles F
    obtain ⟨⟨lower, j⟩, rfl⟩ := B.face_index_surjective triangles G
    change (bipyramidStar source).Adj (index.symm (index (upper, i)))
      (index.symm (index (lower, j))) at indexed
    rw [index.symm_apply_apply, index.symm_apply_apply] at indexed
    rw [placed, placed]
    obtain ⟨_, same_cap | bases⟩ := indexed
    · have same : upper = lower := same_cap.1
      subst lower
      apply (B.face triangles upper i).joined_of_vertex_agreement (B.face triangles upper j)
      rintro x ⟨⟨xI, xJ⟩, vertex⟩
      rcases same_cap.2 with iB | jB
      · have isource : i = source := iB
        subst i
        exact ((net.cap upper).joined j ⟨x, vertex⟩ xJ xI).symm
      · have jsource : j = source := jB
        subst j
        exact (net.cap upper).joined i ⟨x, vertex⟩ xI xJ
    · have iB : i = source := bases.1
      have jB : j = source := bases.2
      subst i
      subst j
      intro x hx
      cases upper <;> cases lower
      · rfl
      · exact (net.bases_joined x ⟨hx.2, hx.1⟩).symm
      · exact net.bases_joined x hx
      · rfl
  · intro F G different
    obtain ⟨⟨upper, i⟩, rfl⟩ := B.face_index_surjective triangles F
    obtain ⟨⟨lower, j⟩, rfl⟩ := B.face_index_surjective triangles G
    rw [placed, placed]
    by_cases same : upper = lower
    · subst lower
      exact (net.cap upper).nonoverlap i j (fun equal => different (congrArg (B.face triangles upper) equal))
    · cases upper <;> cases lower
      · exact False.elim (same rfl)
      · exact (all_cross j i).symm
      · exact all_cross i j
      · exact False.elim (same rfl)

end Development
end SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices
