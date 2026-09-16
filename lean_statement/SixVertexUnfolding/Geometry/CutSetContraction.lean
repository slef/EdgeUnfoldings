import SixVertexUnfolding.Geometry.ClosedCutSet

/-! Removing both multiple-route targets and original vertices other than
the source still leaves a contractible set. The contraction uses actual routes. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Every target outside the explicit cut set has a unique normalized shortest route. -/
theorem unique_outside_cutSet (P : ConvexPolyhedron) (a b : frontier P.body) (outside : b ∉ P.cutSet a) :
    b ∈ P.uniqueTargets a := by
  rw [P.uniqueTargets_eq_complement_multiple a]
  exact fun multiple => outside (Or.inl multiple)

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Every initial target on a shortest route to the complement remains in the complement. -/
theorem chosenGeodesic_avoids_cutSet (a b : frontier P.body) (outside : b ∉ P.cutSet a) (t : unitInterval) :
    P.chosenGeodesic (a, b) t ∉ P.cutSet a := by
  let f := P.chosenGeodesic (a, b)
  have member := P.chosenGeodesic_mem (a, b)
  have first : f 0 = a := congrArg Prod.fst member.2
  have last : f 1 = b := congrArg Prod.snd member.2
  by_cases same : a = b
  · have constant := P.geodesic_same_endpoints f member.1 (first.trans (same.trans last.symm)) t
    change f t ∉ P.cutSet a
    rw [constant, first]
    exact P.source_not_cutSet a
  by_cases at_start : t = 0
  · subst t
    change f 0 ∉ P.cutSet a
    rw [first]
    exact P.source_not_cutSet a
  by_cases at_end : t = 1
  · subst t
    change f 1 ∉ P.cutSet a
    rwa [last]
  have unique := P.chosenGeodesic_stays_unique a b (P.unique_outside_cutSet a b outside) t
  rw [P.uniqueTargets_eq_complement_multiple a] at unique
  rintro (multiple | vertex)
  · exact unique multiple
  · obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f member.1
    exact graph.shortest_lipschitz_avoids_vertices small_faces (P.surfacePathOfCurve f)
      (fun equal => same (first.symm.trans ((Subtype.ext equal).trans last))) shortest finite speed t
      (lt_of_le_of_ne t.property.1 (Ne.symm at_start))
      (lt_of_le_of_ne t.property.2 at_end) vertex.1

include graph small_faces in
/-- The complement of the compact, vertex-augmented cut set contracts to its source along shortest routes. -/
theorem cutSet_complement_contractible (a : frontier P.body) :
    ContractibleSpace {b : frontier P.body // b ∉ P.cutSet a} := by
  let targets : Set (frontier P.body) := {b | b ∉ P.cutSet a}
  let center : targets := ⟨a, P.source_not_cutSet a⟩
  have selected : Continuous (fun b : targets => P.chosenGeodesic (a, b.val)) := by
    have endpoints : Continuous (fun b : targets => (a, b.val)) :=
      continuous_const.prodMk continuous_subtype_val
    apply continuous_iff_continuousAt.mpr
    intro b
    exact ContinuousAt.comp (f := fun c : targets => (a, c.val)) (x := b)
      (P.chosenGeodesic_continuousAt (a, b.val) (P.unique_outside_cutSet a b.val b.property)) endpoints.continuousAt
  let contraction : ContinuousMap.Homotopy (ContinuousMap.const targets center)
      (ContinuousMap.id targets) := {
    toFun := fun pair => ⟨P.chosenGeodesic (a, pair.2.val) pair.1,
      graph.chosenGeodesic_avoids_cutSet small_faces a pair.2.val pair.2.property pair.1⟩
    continuous_toFun := (continuous_eval.comp ((selected.comp continuous_snd).prodMk continuous_fst)).subtype_mk _
    map_zero_left := fun b => Subtype.ext (congrArg Prod.fst (P.chosenGeodesic_mem (a, b.val)).2)
    map_one_left := fun b => Subtype.ext (congrArg Prod.snd (P.chosenGeodesic_mem (a, b.val)).2) }
  apply (contractible_iff_id_nullhomotopic targets).mpr
  exact ⟨center, ⟨contraction.symm⟩⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
