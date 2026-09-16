import SixVertexUnfolding.Geometry.FaceBisectorSegments
import SixVertexUnfolding.Geometry.FaceSegments
import SixVertexUnfolding.Geometry.CutSetInSpace
import SixVertexUnfolding.Geometry.SmallPolyhedronCutBisectors

/-! A finite segment cover for the entire actual cut set in every small-face
polyhedron with at most six vertices. Containment is proved here; exact
segment decomposition and tree structure remain separate obligations. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
theorem small_face_cut_finite_segment_cover (a : frontier P.body) (F : P.Face) :
    ∃ segments : Set P.FaceSegment, segments.Finite ∧
      ∀ x ∈ F.val, x ∈ P.cutSetInSpace a → ∃ s ∈ segments, x ∈ s.points := by
  classical
  let vertices : Set Space := F.val ∩ (P.vertices : Set Space)
  have finite_vertices : vertices.Finite := P.vertices.finite_toSet.subset inter_subset_right
  letI : Finite vertices := finite_vertices
  let chord (pair : vertices × vertices) : P.FaceSegment := {
    face := F, first := pair.1.val, last := pair.2.val
    first_mem := pair.1.property.1, last_mem := pair.2.property.1 }
  let pairs : Set (Plane × Plane) := {pair | pair.1 ∈ P.sourceImages a F ∧
    pair.2 ∈ P.sourceImages a F ∧ pair.1 ≠ pair.2}
  have finite_pairs : pairs.Finite := ((P.sourceImages_finite a F).prod (P.sourceImages_finite a F)).subset
    (fun _ h => ⟨h.1, h.2.1⟩)
  letI : Finite pairs := finite_pairs
  have covers (pair : pairs) := P.face_bisector_segment_cover F pair.val.1 pair.val.2 pair.property.2.2
  choose u hu v hv cover using covers
  let bisector (pair : pairs) : P.FaceSegment := {
    face := F, first := u pair, last := v pair, first_mem := hu pair, last_mem := hv pair }
  refine ⟨range chord ∪ range bisector, (finite_range chord).union (finite_range bisector), ?_⟩
  intro x xF cut
  by_cases vertex : x ∈ P.vertices
  · let w : vertices := ⟨x, xF, vertex⟩
    exact ⟨chord (w, w), Or.inl (mem_range_self _), left_mem_segment ℝ _ _⟩
  · by_cases unique : ∀ G : P.Face, x ∈ G.val → G = F
    · let b : frontier P.body := ⟨x, F.subset_frontier xF⟩
      have multiple : x ∈ P.multipleRouteLocus a :=
        ((P.mem_cutSetInSpace a b).mp cut).resolve_right (fun h => vertex h.1)
      have on_line := small_multiple_routes_on_source_bisectors size small_faces multiple F unique
      obtain ⟨line, member, target⟩ := mem_sUnion.mp on_line
      obtain ⟨p, hp, q, hq, different, rfl⟩ := member
      let pair : pairs := ⟨(p, q), hp, hq, different⟩
      exact ⟨bisector pair, Or.inr (mem_range_self _), cover pair x xF target⟩
    · push Not at unique
      obtain ⟨G, xG, different⟩ := unique
      have shared := F.shareEdge_of_common_nonvertex G different.symm ⟨xF, xG⟩ vertex
      obtain ⟨p, hp, q, hq, _, edge⟩ := F.shared_edge_endpoints G shared
      have pF : p ∈ F.val := (show p ∈ F.val ∩ G.val from edge ▸ left_mem_segment ℝ p q).1
      have qF : q ∈ F.val := (show q ∈ F.val ∩ G.val from edge ▸ right_mem_segment ℝ p q).1
      let pair : vertices × vertices := (⟨p, pF, hp⟩, ⟨q, qF, hq⟩)
      refine ⟨chord pair, Or.inl (mem_range_self _), ?_⟩
      change x ∈ segment ℝ p q
      rw [← edge]
      exact ⟨xF, xG⟩

include size small_faces in
/-- Finitely many straight segments in actual original facets cover the entire cut set. -/
theorem small_cut_finite_segment_cover (a : frontier P.body) :
    ∃ segments : Set P.FaceSegment, segments.Finite ∧
      ∀ x ∈ P.cutSetInSpace a, ∃ s ∈ segments, x ∈ s.points := by
  choose segments finite_segments cover using small_face_cut_finite_segment_cover size small_faces a
  refine ⟨⋃ F, segments F, finite_iUnion finite_segments, ?_⟩
  intro x hx
  obtain ⟨F, xF⟩ := P.boundary_point_in_face (P.cutSetInSpace_subset_boundary a hx)
  obtain ⟨s, hs, member⟩ := cover F x xF hx
  exact ⟨s, mem_iUnion.mpr ⟨F, hs⟩, member⟩

end SixVertexUnfolding.ConvexPolyhedron
