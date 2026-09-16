import SixVertexUnfolding.Geometry.SameSourceLocalNonbranching

/-! Nonbranching propagates along equal-speed shortest rays from one source.
Their final endpoints need not be assumed equal. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set Filter
open scoped Topology

variable {P : ConvexPolyhedron} {a b c : Space}

/-- A shared interior point determines a vertex-free shortest route completely. -/
theorem same_source_agree_of_meeting (first : P.SurfacePath a b) (second : P.SurfacePath a c)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (same_length : first.length = second.length)
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
    obtain ⟨s, u, st, tu, agree⟩ := first.same_source_agree_near_meeting second first_shortest second_shortest
      first_finite second_finite first_speed second_speed same_length t t.property.1 t.property.2 ht
      (avoids_vertices t t.property.1 t.property.2)
    have near : ∀ᶠ v : times in 𝓝 t, (v : unitInterval) ∈ Ioo s u :=
      (continuous_subtype_val.tendsto t).eventually_mem (Ioo_mem_nhds st tu)
    exact mem_of_superset near (fun v hv => agree v ⟨hv.1.le, hv.2.le⟩)
  have all : equal_times = univ := (show IsClopen equal_times from ⟨closed, open_set⟩).eq_univ
    ⟨⟨m, after_start, before_end⟩, meet⟩
  have interior_agrees : Ioo (0 : unitInterval) 1 ⊆ {t | first.curve t = second.curve t} := by
    intro t ht
    have member : (⟨t, ht⟩ : times) ∈ equal_times := by rw [all]; trivial
    exact member
  have limits_agree := closure_minimal interior_agrees
    (isClosed_eq first.curve.continuous second.curve.continuous)
  intro t
  apply limits_agree
  rw [closure_Ioo (by norm_num : (0 : unitInterval) ≠ 1)]
  exact ⟨unitInterval.nonneg t, unitInterval.le_one t⟩

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
