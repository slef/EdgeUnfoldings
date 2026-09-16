import SixVertexUnfolding.Geometry.ShortestSubpaths

/-! A shortest surface route has a finite subdivision into straight portions
in whole original facets. Face entry and exit times supply the subdivision. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set
open scoped ENNReal NNReal

variable {P : ConvexPolyhedron} {a b : Space}

/-- First parameter at which the curve meets a face (one if it never does). -/
noncomputable def faceEntry (path : P.SurfacePath a b) (F : P.Face) : unitInterval :=
  sInf {t | path.curve t ∈ F.val}

/-- Last parameter at which the curve meets a face (zero if it never does). -/
noncomputable def faceExit (path : P.SurfacePath a b) (F : P.Face) : unitInterval :=
  sSup {t | path.curve t ∈ F.val}

/-- Closed facets have closed, compact sets of visit times. -/
theorem face_visits_compact (path : P.SurfacePath a b) (F : P.Face) :
    IsCompact {t : unitInterval | path.curve t ∈ F.val} :=
  (F.isClosed.preimage path.curve.continuous).isCompact

/-- For a shortest path, a visited face occupies its complete entry-to-exit interval. -/
theorem shortest_face_visits_eq_interval (path : P.SurfacePath a b)
    (shortest : path.IsShortest) (finite : path.length ≠ ⊤) (F : P.Face)
    (visited : ∃ t, path.curve t ∈ F.val) :
    {t | path.curve t ∈ F.val} = Icc (path.faceEntry F) (path.faceExit F) := by
  have compact := path.face_visits_compact F
  have first : path.curve (path.faceEntry F) ∈ F.val := compact.sInf_mem visited
  have last : path.curve (path.faceExit F) ∈ F.val := compact.sSup_mem visited
  apply Subset.antisymm
  · intro t ht
    exact ⟨sInf_le ht, le_sSup ht⟩
  · exact (path.shortest_face_visits_ordConnected shortest finite F).out first last

/-- Finitely many face entry and exit times, together with the two endpoints. -/
noncomputable def faceBreaks (path : P.SurfacePath a b) : Finset unitInterval := by
  classical
  letI : Fintype P.Face := Fintype.ofFinite _
  exact {0, 1} ∪ (Finset.univ.image path.faceEntry ∪ Finset.univ.image path.faceExit)

/-- Both ends of the path are subdivision points. -/
theorem faceBreaks_endpoints (path : P.SurfacePath a b) :
    0 ∈ path.faceBreaks ∧ 1 ∈ path.faceBreaks := by
  classical
  simp [faceBreaks]

/-- Every original face contributes its entry and exit times. -/
theorem faceBreaks_contains_face (path : P.SurfacePath a b) (F : P.Face) :
    path.faceEntry F ∈ path.faceBreaks ∧ path.faceExit F ∈ path.faceBreaks := by
  classical
  constructor
  · simp only [faceBreaks, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inl ⟨F, rfl⟩)
  · simp only [faceBreaks, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr ⟨F, rfl⟩)

/-- Consecutive subdivision points bound a portion lying entirely in a single face. -/
theorem shortest_between_faceBreaks (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (s t : unitInterval) (ordered : s < t)
    (consecutive : ∀ u ∈ path.faceBreaks, u ∉ Ioo s t) :
    ∃ F : P.Face, ∀ u ∈ Icc s t, path.curve u ∈ F.val := by
  obtain ⟨r, sr, rt⟩ := exists_between ordered
  obtain ⟨F, hr⟩ := P.boundary_point_in_face (path.on_surface r)
  have interval := path.shortest_face_visits_eq_interval shortest finite F ⟨r, hr⟩
  have r_in : r ∈ Icc (path.faceEntry F) (path.faceExit F) := interval ▸ hr
  have entry : path.faceEntry F ≤ s := by
    by_contra! late
    exact consecutive _ (path.faceBreaks_contains_face F).1 ⟨late, r_in.1.trans_lt rt⟩
  have exit : t ≤ path.faceExit F := by
    by_contra! early
    exact consecutive _ (path.faceBreaks_contains_face F).2 ⟨sr.trans_le r_in.2, early⟩
  refine ⟨F, fun u hu => ?_⟩
  change u ∈ {t | path.curve t ∈ F.val}
  rw [interval]
  exact ⟨entry.trans hu.1, hu.2.trans exit⟩

/-- A shortest path admits a finite subdivision into straight, chord-length face portions.
The condition on consecutive times states that no subdivision point lies strictly between them. -/
theorem shortest_has_finite_face_subdivision (path : P.SurfacePath a b)
    (shortest : path.IsShortest) (finite : path.length ≠ ⊤) :
    ∃ times : Finset unitInterval, 0 ∈ times ∧ 1 ∈ times ∧
      ∀ s ∈ times, ∀ t ∈ times, ∀ ordered : s < t,
        (∀ u ∈ times, u ∉ Ioo s t) →
        ∃ F : P.Face,
          (∀ u ∈ Icc s t, path.curve u ∈ F.val ∧
            path.curve u ∈ segment ℝ (path.curve s) (path.curve t)) ∧
          (path.portion s t ordered.le).length = edist (path.curve s) (path.curve t) := by
  refine ⟨path.faceBreaks, path.faceBreaks_endpoints.1, path.faceBreaks_endpoints.2, ?_⟩
  intro s _ t _ ordered consecutive
  obtain ⟨F, inside⟩ := path.shortest_between_faceBreaks shortest finite s t ordered consecutive
  have hs := inside s ⟨le_rfl, ordered.le⟩
  have ht := inside t ⟨ordered.le, le_rfl⟩
  refine ⟨F, fun u hu => ⟨inside u hu,
    path.shortest_portion_range shortest finite F s t ordered.le hs ht u hu⟩, ?_⟩
  exact (path.portion s t ordered.le).shortest_cofacial_length
    (path.portion_shortest shortest finite s t ordered.le) F hs ht

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
