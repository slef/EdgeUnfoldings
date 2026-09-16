import SixVertexUnfolding.Geometry.SurfacePaths
import SixVertexUnfolding.Geometry.DualConnectivity

/-! Joining face paths gives a finite-length route between any two boundary points. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set
open scoped ENNReal NNReal

namespace SurfacePath

variable {P : ConvexPolyhedron} {a b c : Space}

/-- Traverse the first surface path and then the second. -/
noncomputable def join (first : P.SurfacePath a b) (second : P.SurfacePath b c) : P.SurfacePath a c where
  curve := first.curve.trans second.curve
  on_surface t := by
    rw [Path.trans_apply]
    split_ifs
    · exact first.on_surface _
    · exact second.on_surface _

/-- Concatenation adds lengths, also when either length is infinite. -/
theorem join_length (first : P.SurfacePath a b) (second : P.SurfacePath b c) :
    (first.join second).length = first.length + second.length := by
  have split := eVariationOn.Icc_add_Icc (first.curve.trans second.curve).extend
    (s := Set.univ) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (mem_univ _)
  simp only [univ_inter] at split
  change eVariationOn (first.curve.trans second.curve).extend (Icc 0 1) = _
  rw [← split]
  have left : EqOn (first.curve.trans second.curve).extend
      (first.curve.extend ∘ (fun t : ℝ => 2 * t)) (Icc 0 (1 / 2)) :=
    fun _ ht => Path.extend_trans_of_le_half _ _ ht.2
  have right : EqOn (first.curve.trans second.curve).extend
      (second.curve.extend ∘ (fun t : ℝ => 2 * t - 1)) (Icc (1 / 2) 1) :=
    fun _ ht => Path.extend_trans_of_half_le _ _ ht.1
  rw [eVariationOn.congr left, eVariationOn.congr right,
    eVariationOn.comp_eq_of_monotoneOn _ _ (by intro x hx y hy h; dsimp; linarith),
    eVariationOn.comp_eq_of_monotoneOn _ _ (by intro x hx y hy h; dsimp; linarith)]
  have left_image : (fun t : ℝ => 2 * t) '' Icc 0 (1 / 2) = Icc 0 1 := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩; constructor <;> linarith [hu.1, hu.2]
    · intro ht; refine ⟨t / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by ring⟩
  have right_image : (fun t : ℝ => 2 * t - 1) '' Icc (1 / 2) 1 = Icc 0 1 := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩; constructor <;> linarith [hu.1, hu.2]
    · intro ht; refine ⟨(t + 1) / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by ring⟩
  rw [left_image, right_image]
  rfl

/-- A finite concatenation of rectifiable paths is still rectifiable. -/
theorem join_finite (first : P.SurfacePath a b) (second : P.SurfacePath b c)
    (hfirst : first.length ≠ ⊤) (hsecond : second.length ≠ ⊤) :
    (first.join second).length ≠ ⊤ := by
  rw [join_length]
  exact ENNReal.add_ne_top.mpr ⟨hfirst, hsecond⟩

end SurfacePath

/-- A walk through adjacent whole facets supplies a finite-length surface route. -/
theorem face_walk_has_finite_surface_path (P : ConvexPolyhedron) {F G : P.Face}
    (walk : P.dualGraph.Walk F G) {a b : Space} (ha : a ∈ F.val) (hb : b ∈ G.val) :
    ∃ path : P.SurfacePath a b, path.length ≠ ⊤ := by
  induction walk generalizing a with
  | nil =>
      exact ⟨SurfacePath.inFace _ ha hb, by rw [SurfacePath.inFace_length]; exact edist_ne_top _ _⟩
  | @cons F H G edge tail ih =>
      obtain ⟨u, _, v, _, _, common⟩ := F.shared_edge_endpoints H edge
      have shared : u ∈ F.val ∩ H.val := common ▸ left_mem_segment ℝ u v
      obtain ⟨rest, finite⟩ := ih shared.2 hb
      exact ⟨(SurfacePath.inFace F ha shared.1).join rest,
        SurfacePath.join_finite _ rest (by rw [SurfacePath.inFace_length]; exact edist_ne_top _ _) finite⟩

/-- Any two points on the actual polyhedral boundary can be joined by a rectifiable path. -/
theorem exists_finite_surface_path (P : ConvexPolyhedron) {a b : Space}
    (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body) :
    ∃ path : P.SurfacePath a b, path.length ≠ ⊤ := by
  obtain ⟨F, haF⟩ := P.boundary_point_in_face ha
  obtain ⟨G, hbG⟩ := P.boundary_point_in_face hb
  obtain ⟨walk⟩ := P.dualGraph_connected F G
  exact P.face_walk_has_finite_surface_path walk haF hbG

end SixVertexUnfolding.ConvexPolyhedron
