import SixVertexUnfolding.Geometry.BipyramidHinges

/-! The exact original face adjacencies of a triangular bipyramid. -/

namespace SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices

variable {P : ConvexPolyhedron} (B : BipyramidVertices P)

/-- Noncorresponding triangles on opposite caps meet at just one equator vertex. -/
theorem opposite_caps_intersection
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (i j : Fin 3) (different : i ≠ j) :
    ∃ k : Fin 3, k ≠ i ∧ k ≠ j ∧
      (B.face triangles upper i).val ∩ (B.face triangles (!upper) j).val =
        {(B.equatorVertex k : Space)} := by
  obtain ⟨k, ki, kj, remaining⟩ := remaining_equator_index i j different
  refine ⟨k, ki, kj, ?_⟩
  have common :
      (((B.face triangles upper i).val ∩ (B.face triangles (!upper) j).val) ∩
        (P.vertices : Set Space)) = {(B.equatorVertex k : Space)} := by
    ext x
    constructor
    · rintro ⟨⟨left, right⟩, vertex⟩
      let v : P.Vertex := ⟨x, vertex⟩
      rcases B.vertex_cases_from_pole upper v with pole | opposite | ⟨l, equal⟩
      · have bad : (B.poleVertex upper : Space) ∈ (B.face triangles (!upper) j).val :=
          (congrArg Subtype.val pole) ▸ right
        have excluded : (B.poleVertex upper : Space) ∉ (B.face triangles (!upper) j).val := by
          simpa only [Bool.not_not] using B.opposite_pole_not_mem_face triangles (!upper) j
        exact False.elim (excluded bad)
      · have bad : (B.poleVertex (!upper) : Space) ∈ (B.face triangles upper i).val :=
          (congrArg Subtype.val opposite) ▸ left
        exact False.elim (B.opposite_pole_not_mem_face triangles upper i bad)
      · have li := (B.equator_mem_face triangles upper i l).mp ((congrArg Subtype.val equal) ▸ left)
        have lj := (B.equator_mem_face triangles (!upper) j l).mp ((congrArg Subtype.val equal) ▸ right)
        exact (congrArg Subtype.val equal).trans
          (congrArg (fun m => (B.equatorVertex m : Space)) ((remaining l).mp ⟨li, lj⟩))
    · intro equal
      have same : x = (B.equatorVertex k : Space) := equal
      subst x
      exact ⟨⟨(B.equator_mem_face triangles upper i k).mpr ki,
        (B.equator_mem_face triangles (!upper) j k).mpr kj⟩, (B.equatorVertex k).property⟩
  rw [(B.face triangles upper i).intersection_eq_convexHull_vertices
    (B.face triangles (!upper) j), common, convexHull_singleton]

/-- Across the two caps, an edge is shared exactly when the missing indices agree. -/
theorem opposite_caps_shareEdge_iff
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (i j : Fin 3) :
    P.ShareEdge (B.face triangles upper i) (B.face triangles (!upper) j) ↔ i = j := by
  constructor
  · intro edge
    by_contra different
    obtain ⟨k, _, _, common⟩ := B.opposite_caps_intersection triangles upper i j different
    change affineDimension ((B.face triangles upper i).val ∩ (B.face triangles (!upper) j).val) = 1 at edge
    rw [common, affineDimension_singleton] at edge
    omega
  · rintro rfl
    exact B.across_equator_shareEdge triangles upper i

/-- All nine original facet adjacencies, expressed with the six concrete indices. -/
theorem face_shareEdge_iff
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper lower : Bool) (i j : Fin 3) :
    P.ShareEdge (B.face triangles upper i) (B.face triangles lower j) ↔
      (upper = lower ∧ i ≠ j) ∨ (upper ≠ lower ∧ i = j) := by
  by_cases same : upper = lower
  · subst lower
    simp only [ne_self_iff_false, true_and, false_and, or_false]
    constructor
    · intro edge equal
      subst j
      exact (B.face triangles upper i).shareEdge_irrefl edge
    · exact B.same_cap_shareEdge triangles upper i j
  · have opposite : lower = !upper := by cases upper <;> cases lower <;> simp_all
    rw [opposite, B.opposite_caps_shareEdge_iff]
    cases upper <;> simp

end SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices
