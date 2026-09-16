import SixVertexUnfolding.Geometry.SmallPolyhedronCutSegments
import SixVertexUnfolding.Geometry.SmallPolyhedronCutRetraction
import SixVertexUnfolding.Geometry.SmallPolyhedronJunctions
import SixVertexUnfolding.Geometry.RegularCutTree

/-! The actual cut locus is a finite tree, without choosing a canonical
polyhedron graph. Every junction and original cut vertex is marked, so an
open tree edge contains exactly two shortest routes to each of its points. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Every exact embedded graph of the actual cut set is a tree. -/
theorem small_embedded_cut_graph_isTree (a : frontier P.body)
    (K : P.EmbeddedCutGraph a) : K.graph.IsTree := by
  letI : ContractibleSpace (P.cutSetInSpace a) :=
    small_cutSetInSpace_contractible size small_faces a
  exact ⟨K.connected_of_trace_connected (isConnected_iff_connectedSpace.mpr inferInstance),
    K.acyclic_of_contractible_trace⟩

include size small_faces in
/-- The actual finite cut tree, subdivided at every junction and original cut vertex. -/
theorem small_exists_regular_cut_tree (a : frontier P.body) : Nonempty (P.CutLocusTree a) := by
  let marks : Set Space := Subtype.val '' P.cutExceptions a
  have finite_marks : marks.Finite := (small_cutExceptions_finite size small_faces a).image Subtype.val
  have marks_cut : marks ⊆ P.cutSetInSpace a := by
    rintro _ ⟨b, exceptional, rfl⟩
    exact ⟨b, P.cutExceptions_subset_cutSet a exceptional, rfl⟩
  obtain ⟨K, contains⟩ := small_exists_cut_graph_containing size small_faces a marks finite_marks marks_cut
  exact ⟨{
    toEmbeddedCutGraph := K
    tree := small_embedded_cut_graph_isTree size small_faces a K
    exceptional_vertices := fun b exceptional => contains ⟨b, exceptional, rfl⟩ }⟩

include size small_faces in
/-- Every open tree edge consists of targets with exactly two shortest routes. -/
theorem small_cut_tree_open_edge_two_routes (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (b : frontier P.body)
    (inside : (b : Space) ∈ openSegment ℝ (u : Space) (v : Space)) :
    Nat.card (P.geodesicFiber a b) = 2 := by
  have cut := T.open_edge_cut edge b inside
  have regular := T.open_edge_regular edge b inside
  have different : a ≠ b := by
    rintro rfl
    exact P.source_not_cutSet a cut
  have not_vertex : (b : Space) ∉ P.vertices :=
    fun vertex => regular (Or.inr ⟨vertex, different.symm⟩)
  have multiple : (b : Space) ∈ P.multipleRouteLocus a :=
    cut.resolve_right (fun h => not_vertex h.1)
  have not_unique := ((P.multiple_routes_iff_fiber a b).mp multiple).2
  have lower : ¬ (P.geodesicFiber a b).ncard ≤ 1 := by
    intro bound
    exact not_unique ((ncard_le_one (small_geodesicFiber_finite size small_faces a b different)).mp bound)
  have upper : ¬ 2 < Nat.card (P.geodesicFiber a b) := fun many =>
    regular (Or.inl ((small_junction_iff_route_count size small_faces a b different).mpr many))
  change ¬ Nat.card (P.geodesicFiber a b) ≤ 1 at lower
  omega

end SixVertexUnfolding.ConvexPolyhedron
