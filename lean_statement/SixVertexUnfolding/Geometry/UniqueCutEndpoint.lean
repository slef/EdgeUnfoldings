import SixVertexUnfolding.Geometry.CutSetTerminalRays
import SixVertexUnfolding.Geometry.SameSourceGeodesics
import SixVertexUnfolding.Geometry.GeodesicRescaling

/-! Every point other than the source determines exactly one terminal cut
point along its shortest extension. This uses actual geodesic nonbranching. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem cut_endpoints_agree_of_distance_le (a b c d : frontier P.body) (different : a ≠ b)
    (cut_c : c ∈ P.cutSet a) (cut_d : d ∈ P.cutSet a)
    (through_c : c ∈ P.shortestExtensions a b) (through_d : d ∈ P.shortestExtensions a b)
    (ordered : P.surfaceDist a c ≤ P.surfaceDist a d) : c = d := by
  by_cases cut_b : b ∈ P.cutSet a
  · exact (graph.shortest_extension_of_cut_point small_faces a b c cut_b through_c).trans
      (graph.shortest_extension_of_cut_point small_faces a b d cut_b through_d).symm
  obtain ⟨f, hf, s, at_s⟩ := P.shortest_extension_path a b c through_c
  obtain ⟨g, hg, t, at_t⟩ := P.shortest_extension_path a b d through_d
  have f0 : f 0 = a := congrArg Prod.fst hf.2
  have f1 : f 1 = c := congrArg Prod.snd hf.2
  have g0 : g 0 = a := congrArg Prod.fst hg.2
  have g1 : g 1 = d := congrArg Prod.snd hg.2
  have ac : a ≠ c := fun same => P.source_not_cutSet a (same.symm ▸ cut_c)
  have ad : a ≠ d := fun same => P.source_not_cutSet a (same.symm ▸ cut_d)
  have lc : 0 < P.surfaceDist a c := lt_of_le_of_ne (P.surfaceDist_nonneg a c)
    (fun zero => ac (Subtype.ext ((P.surfaceDist_eq_zero_iff a.property c.property).mp zero.symm)))
  have ld : 0 < P.surfaceDist a d := lt_of_le_of_ne (P.surfaceDist_nonneg a d)
    (fun zero => ad (Subtype.ext ((P.surfaceDist_eq_zero_iff a.property d.property).mp zero.symm)))
  let r : unitInterval := ⟨P.surfaceDist a c / P.surfaceDist a d,
    (div_pos lc ld).le, (div_le_one ld).mpr ordered⟩
  have scaled : P.surfaceDist a d * (r : ℝ) = P.surfaceDist a c := by
    dsimp [r]
    field_simp
  have s_positive : 0 < s := lt_of_le_of_ne s.property.1 (by
    intro zero
    have equal : s = 0 := zero.symm
    rw [equal, f0] at at_s
    exact different at_s)
  have s_before : s < 1 := lt_of_le_of_ne s.property.2 (by
    intro one
    have equal : s = 1 := one
    rw [equal, f1] at at_s
    exact cut_b (at_s ▸ cut_c))
  have first_distance := P.geodesic_source_distance f hf.1 s
  have second_distance := P.geodesic_source_distance g hg.1 t
  rw [f0, f1, at_s] at first_distance
  rw [g0, g1, at_t] at second_distance
  have same_time : r * s = t := by
    apply Subtype.ext
    change (r : ℝ) * (s : ℝ) = (t : ℝ)
    apply mul_left_cancel₀ ld.ne'
    calc
      P.surfaceDist a d * ((r : ℝ) * (s : ℝ)) = P.surfaceDist a c * (s : ℝ) := by
        rw [← mul_assoc, scaled]
      _ = P.surfaceDist a d * (t : ℝ) := first_distance.symm.trans second_distance
  have equal := graph.same_source_geodesics_agree small_faces f (P.geodesicPrefix g r)
    hf.1 (P.geodesicPrefix_geodesic g hg.1 r)
    (by simpa only [f0, f1] using ac)
    (by simp only [P.geodesicPrefix_apply, mul_zero, f0, g0])
    (by simp only [P.geodesicPrefix_apply, mul_zero, mul_one]
        rw [P.geodesic_source_distance g hg.1 r, f0, f1, g0, g1, scaled])
    s s_positive s_before (by rw [P.geodesicPrefix_apply, same_time, at_s, at_t])
  have endpoint : c = g r := by
    have value := congrArg (fun h : P.BoundaryCurve => h 1) equal
    simpa only [f1, P.geodesicPrefix_apply, mul_one] using value
  have extends_c := P.geodesic_endpoint_extension g hg.1 r
  rw [g0, g1, ← endpoint] at extends_c
  exact (graph.shortest_extension_of_cut_point small_faces a c d cut_c extends_c).symm

include graph small_faces in
/-- Shortest extensions through a point other than the source have a unique cut endpoint. -/
theorem cut_endpoint_unique (a b c d : frontier P.body) (different : a ≠ b)
    (cut_c : c ∈ P.cutSet a) (cut_d : d ∈ P.cutSet a)
    (through_c : c ∈ P.shortestExtensions a b) (through_d : d ∈ P.shortestExtensions a b) : c = d := by
  rcases le_total (P.surfaceDist a c) (P.surfaceDist a d) with ordered | ordered
  · exact graph.cut_endpoints_agree_of_distance_le small_faces a b c d different cut_c cut_d through_c through_d ordered
  · exact (graph.cut_endpoints_agree_of_distance_le small_faces a b d c different cut_d cut_c through_d through_c ordered).symm

include graph small_faces in
/-- The terminal cut endpoint exists and is unique. -/
theorem exists_unique_cut_endpoint (a b : frontier P.body) (different : a ≠ b) :
    ∃! c : frontier P.body, c ∈ P.cutSet a ∧ c ∈ P.shortestExtensions a b := by
  obtain ⟨c, cut, extension⟩ := graph.exists_shortest_extension_in_cutSet small_faces a b different
  exact ⟨c, ⟨cut, extension⟩, fun d hd =>
    graph.cut_endpoint_unique small_faces a b d c different hd.1 cut hd.2 extension⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
