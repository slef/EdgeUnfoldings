import SixVertexUnfolding.Geometry.TetrahedronFaces

/-! Every pair of tetrahedron facets shares an original edge; a face star supplies the hinges. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- In a tetrahedron, two opposite-vertex facets share precisely the other two vertices. -/
theorem oppositeFaces_common_vertices (P : ConvexPolyhedron) (size : P.vertices.card = 4)
    (v w : P.Vertex) :
    ((P.oppositeFace size v).val ∩ (P.oppositeFace size w).val) ∩ (P.vertices : Set Space) =
      (P.vertices : Set Space) \ {(v : Space), (w : Space)} := by
  have rearrange :
      ((P.oppositeFace size v).val ∩ (P.oppositeFace size w).val) ∩ (P.vertices : Set Space) =
      ((P.oppositeFace size v).val ∩ (P.vertices : Set Space)) ∩
        ((P.oppositeFace size w).val ∩ (P.vertices : Set Space)) := by
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  rw [rearrange, P.oppositeFace_vertices, P.oppositeFace_vertices]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_singleton_iff, Set.mem_insert_iff]
  tauto

/-- Every two different tetrahedron facets share a complete original edge. -/
theorem tetrahedron_faces_shareEdge (P : ConvexPolyhedron) (size : P.vertices.card = 4)
    (F G : P.Face) (distinct : F ≠ G) : P.ShareEdge F G := by
  obtain ⟨v, rfl⟩ := (P.oppositeFace_bijective size).surjective F
  obtain ⟨w, rfl⟩ := (P.oppositeFace_bijective size).surjective G
  have different : v ≠ w := fun same => distinct (congrArg (P.oppositeFace size) same)
  have different_points : (v : Space) ≠ (w : Space) := fun same => different (Subtype.ext same)
  have count : ((P.vertices : Set Space) \ {(v : Space), (w : Space)}).ncard = 2 := by
    rw [Set.ncard_diff (by rintro x (rfl | rfl); exacts [v.property, w.property]),
      Set.ncard_coe_finset, Set.ncard_pair different_points, size]
  obtain ⟨a, b, ab, pair⟩ := Set.ncard_eq_two.mp count
  change affineDimension ((P.oppositeFace size v).val ∩ (P.oppositeFace size w).val) = 1
  rw [(P.oppositeFace size v).intersection_eq_convexHull_vertices (P.oppositeFace size w),
    P.oppositeFaces_common_vertices, pair, affineDimension_convexHull]
  exact affineDimension_pair ab

/-- A tetrahedron has a spanning hinge tree whose every hinge joins the chosen base facet. -/
theorem exists_tetrahedron_face_star (P : ConvexPolyhedron) (size : P.vertices.card = 4)
    (base : P.Face) :
    ∃ hinges : SimpleGraph P.Face, hinges.IsTree ∧ hinges ≤ P.dualGraph ∧
      ∀ F G, hinges.Adj F G → F = base ∨ G = base := by
  let star : SimpleGraph P.Face := {
    Adj := fun F G => F ≠ G ∧ (F = base ∨ G = base)
    symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  have star_connected : star.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨base, ?_⟩
    intro F
    by_cases same : base = F
    · subst F
      exact SimpleGraph.Reachable.rfl
    · exact (show star.Adj base F from ⟨same, Or.inl rfl⟩).reachable
  obtain ⟨hinges, inside_star, tree⟩ := star_connected.exists_isTree_le
  refine ⟨hinges, tree, ?_, ?_⟩
  · intro F G adjacent
    exact P.tetrahedron_faces_shareEdge size F G (inside_star adjacent).1
  · intro F G adjacent
    exact (inside_star adjacent).2

end SixVertexUnfolding.ConvexPolyhedron
