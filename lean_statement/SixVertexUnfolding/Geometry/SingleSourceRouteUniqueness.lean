import SixVertexUnfolding.Geometry.UniqueRouteSourceDistance

/-! A local single-source distance formula is equivalent to route uniqueness
at a distinct target in the interior of one face. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- A local planar source-distance formula forces the actual shortest route to be unique. -/
theorem unique_route_of_local_source_formula (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F)
    (source : Plane) (U : Set Space) (openU : IsOpen U) (bU : (b : Space) ∈ U)
    (formula : ∀ x ∈ U ∩ frontier P.body, P.surfaceDist a x = dist source (P.faceCoordinates F x)) :
    (P.geodesicFiber a b).Subsingleton := by
  intro f hf g hg
  obtain ⟨first, hs, fs, cs, first_eq⟩ := P.geodesicFiber_path a b f hf
  obtain ⟨second, ht, ft, ct, second_eq⟩ := P.geodesicFiber_path a b g hg
  obtain ⟨V, openV, bV, in_face⟩ := P.unique_face_neighborhood F unique_face
  have agree := first.agree_of_terminal_distance_formula second hs ht fs ft cs ct
    (graph.shortest_lipschitz_avoids_vertices small_faces first
      (fun h => different (Subtype.ext h)) hs fs cs) F source (U ∩ V) (openU.inter openV) ⟨bU, bV⟩
    (fun _ hx => (in_face _ ⟨hx.1.2, hx.2⟩).1) (fun _ hx => formula _ ⟨hx.1.1, hx.2⟩)
  rw [← first_eq, ← second_eq, first.eq_of_curve_eq second agree]

include graph small_faces in
/-- Route uniqueness is exactly the existence of a local single-source formula. -/
theorem unique_route_iff_local_source_formula (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    (P.geodesicFiber a b).Subsingleton ↔
      ∃ source : Plane, ∃ U : Set Space, IsOpen U ∧ (b : Space) ∈ U ∧
        ∀ x ∈ U ∩ frontier P.body, P.surfaceDist a x = dist source (P.faceCoordinates F x) := by
  constructor
  · intro unique
    obtain ⟨source, _, U, openU, bU, formula⟩ := graph.unique_route_source_distance small_faces a b different F unique_face unique
    exact ⟨source, U, openU, bU, formula⟩
  · rintro ⟨source, U, openU, bU, formula⟩
    exact graph.unique_route_of_local_source_formula small_faces a b different F unique_face source U openU bU formula

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
