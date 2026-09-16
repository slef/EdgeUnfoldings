import SixVertexUnfolding.Geometry.MaximalRaysReachCutSet
import SixVertexUnfolding.Geometry.UniqueRouteDensity

/-! The cut set consists exactly of final shortest-ray endpoints. In
particular, a shortest route cannot run through a cut point and continue. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Proper prefixes of every shortest route avoid the vertex-augmented cut set. -/
theorem geodesic_proper_prefix_outside_cutSet (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (t : unitInterval) (before : t < 1) : f t ∉ P.cutSet (f 0) := by
  by_cases at_start : t = 0
  · subst t
    exact P.source_not_cutSet (f 0)
  rintro (multiple | vertex)
  · exact graph.shortest_route_avoids_multiple_locus small_faces f geodesic different t before multiple
  · obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
    exact graph.shortest_lipschitz_avoids_vertices small_faces (P.surfacePathOfCurve f)
      (fun equal => different (Subtype.ext equal)) shortest finite speed t
      (lt_of_le_of_ne t.property.1 (Ne.symm at_start)) before vertex.1

include graph small_faces in
/-- A shortest extension through a cut point has that very point as its endpoint. -/
theorem shortest_extension_of_cut_point (a b c : frontier P.body) (cut : b ∈ P.cutSet a)
    (extension : c ∈ P.shortestExtensions a b) : c = b := by
  obtain ⟨f, hf, t, at_t⟩ := P.shortest_extension_path a b c extension
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = c := congrArg Prod.snd hf.2
  have different : f 0 ≠ f 1 := by
    intro equal
    have at_start := P.geodesic_same_endpoints f hf.1 equal t
    rw [at_t, first] at at_start
    exact P.source_not_cutSet a (at_start ▸ cut)
  by_contra cb
  have before : t < 1 := lt_of_le_of_ne t.property.2 (fun one => cb (by simpa only [one, last] using at_t))
  have outside := graph.geodesic_proper_prefix_outside_cutSet small_faces f hf.1 different t before
  rw [first, at_t] at outside
  exact outside cut

include graph small_faces in
/-- Away from the source, being in the cut set means having no strict shortest extension. -/
theorem cutSet_iff_terminal (a b : frontier P.body) (different : a ≠ b) :
    b ∈ P.cutSet a ↔ ∀ c ∈ P.shortestExtensions a b, c = b := by
  constructor
  · exact fun cut c extension => graph.shortest_extension_of_cut_point small_faces a b c cut extension
  · intro terminal
    by_contra outside
    obtain ⟨c, extension, different_c⟩ := graph.shortest_extension_outside_cutSet small_faces a b different outside
    exact different_c (terminal c extension)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
