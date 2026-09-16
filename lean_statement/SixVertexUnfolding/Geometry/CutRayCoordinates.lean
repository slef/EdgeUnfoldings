import SixVertexUnfolding.Geometry.CutEndpointRetraction

/-! A nonsource interior point determines its terminal cut point, its
normalized time, and its entire shortest route. These are the uniqueness
facts for the radial surface partition. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A normalized shortest route with distinct endpoints is injective. -/
theorem geodesicFiber_injective (P : ConvexPolyhedron) (a b : frontier P.body) (different : a ≠ b)
    (f : P.BoundaryCurve) (member : f ∈ P.geodesicFiber a b) : Function.Injective f := by
  have f0 : f 0 = a := congrArg Prod.fst member.2
  have f1 : f 1 = b := congrArg Prod.snd member.2
  have length_ne : P.surfaceDist a b ≠ 0 := fun zero =>
    different (Subtype.ext ((P.surfaceDist_eq_zero_iff a.property b.property).mp zero))
  intro s t same
  have distance := member.1 s t
  rw [f0, f1, same, P.surfaceDist_self (f t).property] at distance
  exact dist_eq_zero.mp ((mul_eq_zero.mp distance.symm).resolve_left length_ne)

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Two routes to terminal cut points that meet before the end are the same ray with the same parameter. -/
theorem cut_rays_meeting (a b c : frontier P.body) (cut_b : b ∈ P.cutSet a) (cut_c : c ∈ P.cutSet a)
    (f g : P.BoundaryCurve) (hf : f ∈ P.geodesicFiber a b) (hg : g ∈ P.geodesicFiber a c)
    (s t : unitInterval) (positive : 0 < s) (before : s < 1) (meet : f s = g t) :
    b = c ∧ s = t ∧ f = g := by
  have f0 : f 0 = a := congrArg Prod.fst hf.2
  have f1 : f 1 = b := congrArg Prod.snd hf.2
  have g0 : g 0 = a := congrArg Prod.fst hg.2
  have g1 : g 1 = c := congrArg Prod.snd hg.2
  have different : a ≠ b := fun same => P.source_not_cutSet a (same.symm ▸ cut_b)
  have nonzero_point : a ≠ f s := by
    intro same
    have time_zero := P.geodesicFiber_injective a b different f hf (f0.trans same)
    exact positive.ne time_zero
  have through_b := P.geodesic_endpoint_extension f hf.1 s
  have through_c := P.geodesic_endpoint_extension g hg.1 t
  rw [f0, f1] at through_b
  rw [g0, g1, ← meet] at through_c
  have endpoints := graph.cut_endpoint_unique small_faces a (f s) b c nonzero_point
    cut_b cut_c through_b through_c
  have length_ne : P.surfaceDist a b ≠ 0 := fun zero =>
    different (Subtype.ext ((P.surfaceDist_eq_zero_iff a.property b.property).mp zero))
  have first_distance := P.geodesic_source_distance f hf.1 s
  have second_distance := P.geodesic_source_distance g hg.1 t
  rw [f0, f1, meet] at first_distance
  rw [g0, g1, ← endpoints] at second_distance
  have times : s = t := Subtype.ext (mul_left_cancel₀ length_ne (first_distance.symm.trans second_distance))
  refine ⟨endpoints, times, ?_⟩
  apply graph.geodesic_curves_agree_of_meeting small_faces f g hf.1 hg.1
    (by simpa only [f0, f1] using different) (f0.trans g0.symm) ((f1.trans endpoints).trans g1.symm)
    s positive before
  simpa only [times] using meet

include graph small_faces in
/-- Following any shortest route toward its cut endpoint recovers that endpoint under the retraction. -/
theorem cutEndpoint_on_route (a b : frontier P.body) (cut_b : b ∈ P.cutSet a)
    (f : P.BoundaryCurve) (hf : f ∈ P.geodesicFiber a b) (t : unitInterval) (positive : 0 < t) :
    ∃ different : f t ≠ a, (graph.cutEndpoint small_faces a ⟨f t, different⟩).val = b := by
  have f0 : f 0 = a := congrArg Prod.fst hf.2
  have f1 : f 1 = b := congrArg Prod.snd hf.2
  have distinct : a ≠ b := fun same => P.source_not_cutSet a (same.symm ▸ cut_b)
  have different : f t ≠ a := by
    intro same
    have equal := P.geodesicFiber_injective a b distinct f hf (same.trans f0.symm)
    exact positive.ne' equal
  refine ⟨different, ?_⟩
  have extension := P.geodesic_endpoint_extension f hf.1 t
  rw [f0, f1] at extension
  exact graph.cut_endpoint_unique small_faces a (f t) _ b different.symm
    (graph.cutEndpoint small_faces a ⟨f t, different⟩).property cut_b
    (graph.cutEndpoint_extension small_faces a ⟨f t, different⟩) extension

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
