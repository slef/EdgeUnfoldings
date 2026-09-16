import SixVertexUnfolding.Geometry.RetainedRadialPaths
import SixVertexUnfolding.Geometry.SmallPolyhedronStarCutEndpoints

/-! Every retained surface point can move along its actual shortest ray
to a nonvertex point of the cut locus, without crossing a star cut.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Following the remainder of a shortest ray stays within the retained surface. -/
theorem small_retained_point_joins_cut_locus {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (a : frontier P.body)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (b : P.UncutSurface a) :
    ∃ c : frontier P.body, c ∈ P.cutSet a ∧ (c : Space) ∉ P.vertices ∧
      JoinedIn (P.starCuts a)ᶜ b.val c := by
  have different : b.val ≠ a := fun same => b.property (same.symm ▸ P.source_mem_starCuts a)
  let c := small_cutEndpoint size small_faces a ⟨b.val, different⟩
  have nonvertex : (c.val : Space) ∉ P.vertices := fun original => b.property
    ((small_cutEndpoint_original_iff_starCut size small_faces a cofacial ⟨b.val, different⟩).mp original)
  obtain ⟨route, member, t, at_b⟩ := P.shortest_extension_path a b.val c.val
    (small_cutEndpoint_extension size small_faces a ⟨b.val, different⟩)
  have positive : 0 < t := by
    apply lt_of_le_of_ne t.property.1
    intro zero
    have equal : (0 : unitInterval) = t := Subtype.ext zero
    exact different (at_b.symm.trans (equal ▸ congrArg Prod.fst member.2))
  let time (s : unitInterval) : unitInterval :=
    ⟨(1 - (s : ℝ)) * (t : ℝ) + (s : ℝ), by
      constructor
      · exact add_nonneg (mul_nonneg (sub_nonneg.mpr s.property.2) t.property.1) s.property.1
      · nlinarith [mul_nonneg (sub_nonneg.mpr s.property.2) (sub_nonneg.mpr t.property.2)]⟩
  have time_zero : time 0 = t := by apply Subtype.ext; simp [time]
  have time_one : time 1 = 1 := by apply Subtype.ext; simp [time]
  have time_positive (s : unitInterval) : 0 < time s := by
    change 0 < (1 - (s : ℝ)) * (t : ℝ) + (s : ℝ)
    have tp : (0 : ℝ) < t := positive
    nlinarith [mul_nonneg s.property.1 (sub_nonneg.mpr t.property.2)]
  let path : Path b.val c.val := {
    toFun := fun s => route (time s)
    continuous_toFun := route.continuous.comp (by fun_prop)
    source' := by rw [time_zero]; exact at_b
    target' := by rw [time_one]; exact congrArg Prod.snd member.2 }
  exact ⟨c.val, c.property, nonvertex, path, fun s =>
    small_nonvertex_terminal_ray_uncut size small_faces a c.val cofacial c.property nonvertex
      route member (time s) (time_positive s)⟩

end SixVertexUnfolding.ConvexPolyhedron
