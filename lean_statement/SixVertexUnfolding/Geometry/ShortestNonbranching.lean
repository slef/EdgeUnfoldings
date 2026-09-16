import SixVertexUnfolding.Geometry.ShortestLocalNonbranching

/-! Local uniqueness propagates along shortest routes whose interiors avoid
the original vertices. Vertex avoidance remains a separate geometric obligation. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set Filter
open scoped Topology

variable {P : ConvexPolyhedron} {a b : Space}

/-- A shared interior point determines a vertex-free shortest route completely. -/
theorem agree_of_interior_meeting (first second : P.SurfacePath a b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (avoids_vertices : ∀ t : unitInterval, 0 < t → t < 1 → first.curve t ∉ P.vertices)
    (m : unitInterval) (after_start : 0 < m) (before_end : m < 1)
    (meet : first.curve m = second.curve m) : ∀ t, first.curve t = second.curve t := by
  let times := Ioo (0 : unitInterval) 1
  letI : PreconnectedSpace times := Subtype.preconnectedSpace isPreconnected_Ioo
  let equal_times : Set times := {t | first.curve t = second.curve t}
  have closed : IsClosed equal_times := isClosed_eq
    (first.curve.continuous.comp continuous_subtype_val) (second.curve.continuous.comp continuous_subtype_val)
  have open_set : IsOpen equal_times := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨s, u, st, tu, agree⟩ := first.agree_near_nonvertex_meeting second first_shortest second_shortest
      first_finite second_finite first_speed second_speed t t.property.1 t.property.2 ht
      (avoids_vertices t t.property.1 t.property.2)
    have near : ∀ᶠ v : times in 𝓝 t, (v : unitInterval) ∈ Ioo s u :=
      (continuous_subtype_val.tendsto t).eventually_mem (Ioo_mem_nhds st tu)
    exact mem_of_superset near (fun v hv => agree v ⟨hv.1.le, hv.2.le⟩)
  have all : equal_times = univ := (show IsClopen equal_times from ⟨closed, open_set⟩).eq_univ
    ⟨⟨m, after_start, before_end⟩, meet⟩
  intro t
  by_cases at_start : t = 0
  · subst t
    rw [first.curve.source, second.curve.source]
  by_cases at_end : t = 1
  · subst t
    rw [first.curve.target, second.curve.target]
  have inside : t ∈ times :=
    ⟨lt_of_le_of_ne unitInterval.nonneg' (fun same => at_start same.symm),
      lt_of_le_of_ne unitInterval.le_one' at_end⟩
  have member : (⟨t, inside⟩ : times) ∈ equal_times := by rw [all]; trivial
  exact member

/-- The length of a finite route with distinct endpoints is strictly positive. -/
theorem length_toReal_pos (path : P.SurfacePath a b) (different : a ≠ b) (finite : path.length ≠ ⊤) :
    0 < path.length.toReal := ENNReal.toReal_pos (by
      intro zero
      have bound := path.chord_le_length
      rw [zero] at bound
      exact different (edist_eq_zero.mp (le_antisymm bound bot_le))) finite

/-- Two equally parametrized shortest routes reach a common point at the same time. -/
theorem meeting_parameters_equal (first second : P.SurfacePath a b) (different : a ≠ b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (s t : unitInterval) (meet : first.curve s = second.curve t) : s = t := by
  have front := first.source_distance first_shortest first_finite first_speed s
  have back := second.source_distance second_shortest second_finite second_speed t
  rw [meet, back, ← first.shortest_lengths_equal second first_shortest second_shortest] at front
  apply Subtype.ext
  exact (mul_left_cancel₀ (first.length_toReal_pos different first_finite).ne' front).symm

/-- Distinct shortest routes with vertex-free interiors have disjoint open traces. -/
theorem disjoint_open_traces (first second : P.SurfacePath a b) (different : a ≠ b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (avoids_vertices : ∀ t : unitInterval, 0 < t → t < 1 → first.curve t ∉ P.vertices)
    (distinct_routes : ¬ ∀ t, first.curve t = second.curve t) :
    Disjoint (first.curve '' Ioo (0 : unitInterval) 1) (second.curve '' Ioo (0 : unitInterval) 1) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨s, hs, first_at⟩ ⟨t, ht, second_at⟩
  have meet := first_at.trans second_at.symm
  have same := first.meeting_parameters_equal second different first_shortest second_shortest
    first_finite second_finite first_speed second_speed s t meet
  subst t
  exact distinct_routes (first.agree_of_interior_meeting second first_shortest second_shortest
    first_finite second_finite first_speed second_speed avoids_vertices s hs.1 hs.2 meet)

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
