import SixVertexUnfolding.Geometry.CutLineArcs

/-! The regular cut arcs have no self-identifications and no isolated
central points. Consequently any isolated cut points belong to the finite exceptions. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutArc

variable {P : ConvexPolyhedron} {a b : Space} (arc : P.CutArc a b)

theorem injective : InjOn arc.curve (Ioo (-arc.radius) arc.radius) := by
  intro s hs t ht same
  apply dist_eq_zero.mp
  rw [← arc.distance s hs t ht, same, P.surfaceDist_self (arc.on_surface t ht)]

include arc in
/-- Every open neighborhood of the central point contains another point of this cut arc. -/
theorem other_point_nearby (U : Set Space) (openU : IsOpen U) (bU : b ∈ U) :
    ∃ y ∈ U ∩ frontier P.body, y ∈ P.multipleRouteLocus a ∧ y ≠ b := by
  have zero_in : (0 : ℝ) ∈ Ioo (-arc.radius) arc.radius := ⟨neg_neg_of_pos arc.positive, arc.positive⟩
  obtain ⟨δ, positive, near⟩ := Metric.isOpen_iff.mp
    (openU.preimage arc.continuous) 0 (by simpa only [mem_preimage, arc.at_zero] using bU)
  let t := min arc.radius δ / 2
  have t_pos : 0 < t := half_pos (lt_min arc.positive positive)
  have t_radius : t < arc.radius := by
    have := min_le_left arc.radius δ
    dsimp [t]
    linarith [arc.positive]
  have t_delta : t < δ := by
    have := min_le_right arc.radius δ
    dsimp [t]
    linarith
  have interval : t ∈ Ioo (-arc.radius) arc.radius := ⟨by linarith [arc.positive], t_radius⟩
  refine ⟨arc.curve t, ⟨near ?_, arc.on_surface t interval⟩, arc.on_cut t interval, ?_⟩
  · change dist t 0 < δ
    simpa only [Real.dist_eq, sub_zero, abs_of_pos t_pos] using t_delta
  · intro same
    have equal : t = 0 := arc.injective interval zero_in (same.trans arc.at_zero.symm)
    exact t_pos.ne' equal

end CutArc

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Any isolated point of the compact cut set is one of the finitely many exceptional points. -/
theorem isolated_cut_point_exceptional (a b : frontier P.body) (cut : b ∈ P.cutSet a)
    (U : Set (frontier P.body)) (openU : IsOpen U) (bU : b ∈ U)
    (isolated : ∀ c ∈ U ∩ P.cutSet a, c = b) : b ∈ P.cutExceptions a := by
  by_contra regular
  obtain ⟨arc⟩ := graph.regular_cut_arc small_faces a b cut regular
  obtain ⟨V, openV, sameV⟩ := isOpen_induced_iff.mp openU
  have bV : (b : Space) ∈ V := by
    change b ∈ Subtype.val ⁻¹' V
    rwa [sameV]
  obtain ⟨y, hy, multiple, different⟩ := arc.other_point_nearby V openV bV
  let c : frontier P.body := ⟨y, hy.2⟩
  have cU : c ∈ U := by rw [← sameV]; exact hy.1
  exact different (congrArg Subtype.val (isolated c ⟨cU, Or.inl multiple⟩))

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
