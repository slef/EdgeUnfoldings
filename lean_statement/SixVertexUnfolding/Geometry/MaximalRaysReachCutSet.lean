import SixVertexUnfolding.Geometry.NoncutRayExtension
import SixVertexUnfolding.Geometry.ShortestExtensionPaths

/-! Farthest shortest extensions terminate in the actual cut set, with a
genuine shortest route joining the source, the prescribed point, and that endpoint. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- A farthest shortest extension through a point different from the source must end in the cut set. -/
theorem farthest_shortest_extension_in_cutSet (a b c : frontier P.body) (different : a ≠ b)
    (extension : c ∈ P.shortestExtensions a b)
    (farthest : ∀ d ∈ P.shortestExtensions a b, P.surfaceDist a d ≤ P.surfaceDist a c) :
    c ∈ P.cutSet a := by
  have ac : a ≠ c := by
    intro same
    have equal := extension
    change P.surfaceDist a c = P.surfaceDist a b + P.surfaceDist b c at equal
    rw [← same, P.surfaceDist_self a.property] at equal
    have zero : P.surfaceDist a b = 0 := by
      linarith [P.surfaceDist_nonneg a b, P.surfaceDist_nonneg b a]
    exact different (Subtype.ext ((P.surfaceDist_eq_zero_iff a.property b.property).mp zero))
  by_contra outside
  obtain ⟨d, through_c, dc⟩ := graph.shortest_extension_outside_cutSet small_faces a c ac outside
  have bound := farthest d (P.shortestExtensions_trans a b c d extension through_c)
  have positive : 0 < P.surfaceDist c d := lt_of_le_of_ne (P.surfaceDist_nonneg c d)
    (fun zero => dc (Subtype.ext ((P.surfaceDist_eq_zero_iff c.property d.property).mp zero.symm)).symm)
  change P.surfaceDist a d = P.surfaceDist a c + P.surfaceDist c d at through_c
  linarith

include graph small_faces in
/-- Every point other than the source lies on a shortest ray ending in the actual cut set. -/
theorem exists_shortest_extension_in_cutSet (a b : frontier P.body) (different : a ≠ b) :
    ∃ c ∈ P.cutSet a, c ∈ P.shortestExtensions a b := by
  obtain ⟨c, extension, farthest⟩ := P.exists_farthest_shortest_extension a b
  exact ⟨c, graph.farthest_shortest_extension_in_cutSet small_faces a b c different extension farthest, extension⟩

include graph small_faces in
/-- The extension to the cut set is realized by a normalized shortest surface route through `b`. -/
theorem exists_cut_endpoint_route (a b : frontier P.body) (different : a ≠ b) :
    ∃ c ∈ P.cutSet a, ∃ f ∈ P.geodesicFiber a c, ∃ t : unitInterval, f t = b := by
  obtain ⟨c, cut, extension⟩ := graph.exists_shortest_extension_in_cutSet small_faces a b different
  obtain ⟨f, hf, t, at_t⟩ := P.shortest_extension_path a b c extension
  exact ⟨c, cut, f, hf, t, at_t⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
