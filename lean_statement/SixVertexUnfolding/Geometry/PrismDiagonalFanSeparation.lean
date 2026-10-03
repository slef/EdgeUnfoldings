import SixVertexUnfolding.Geometry.PrismDiagonalVertexFans

/-! Transfer the four-corner cone separation to the actual original polygons. -/

namespace SixVertexUnfolding.Prism

open FaceLabel

/-- After the two four-face fans, these three pairs remain. -/
def fallbackHardPairs : Finset (Sym2 FaceLabel) := {s(A, B), s(B, D), s(D, F)}

end SixVertexUnfolding.Prism

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4}
variable (prism_kind : graph.kind = .prismDiagonal)
variable (net : graph.PrismFallbackDevelopment small_faces)
include prism_kind

/-- Every point of each whole polygon lies inside its actual corner cone. -/
theorem PrismFallbackDevelopment.face_subset_vertexFan_cone (q : Fin 2) (k : Fin 4) :
    net.place (fanFace q k) '' (graph.prismDiagonalFace small_faces (fanFace q k)).val ⊆
      (net.vertexFan prism_kind q).cornerCone k := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨l, r, aL, bL, cL, aR, cR, bR⟩ := (by decide : ∀ q k,
    ∃ l r : FaceLabel,
      fanCenter q ∈ faceVertices l ∧ fanRayLabel q k.castSucc ∈ faceVertices l ∧
      fanRayLabel q k.succ ∉ faceVertices l ∧
      fanCenter q ∈ faceVertices r ∧ fanRayLabel q k.succ ∈ faceVertices r ∧
      fanRayLabel q k.castSucc ∉ faceVertices r) q k
  have members := (by decide : ∀ q k,
    fanCenter q ∈ faceVertices (fanFace q k) ∧
    fanRayLabel q k.castSucc ∈ faceVertices (fanFace q k) ∧
    fanRayLabel q k.succ ∈ faceVertices (fanFace q k)) q k
  have distinct := (by decide : ∀ q k,
    fanCenter q ≠ fanRayLabel q k.castSucc ∧ fanCenter q ≠ fanRayLabel q k.succ ∧
    fanRayLabel q k.castSucc ≠ fanRayLabel q k.succ) q k
  have on_face (f : FaceLabel) (i : Fin 6) := graph.prismVertex_mem_face small_faces prism_kind f i
  have noncollinear := P.no_three_collinear_vertices
    (graph.prismVertex (fanCenter q)).property (graph.prismVertex (fanRayLabel q k.castSucc)).property
    (graph.prismVertex (fanRayLabel q k.succ)).property
    (graph.prismVertex_injective.ne distinct.1) (graph.prismVertex_injective.ne distinct.2.1)
    (graph.prismVertex_injective.ne distinct.2.2)
  obtain ⟨t, u, ht, hu, coords⟩ :=
    (graph.prismDiagonalFace small_faces (fanFace q k)).nonnegative_corner_coordinates_of_facets
      (graph.prismDiagonalFace small_faces l) (graph.prismDiagonalFace small_faces r)
      (graph.prismVertex (fanCenter q)) (graph.prismVertex (fanRayLabel q k.castSucc))
      (graph.prismVertex (fanRayLabel q k.succ)) x
      ((on_face _ _).mpr members.1) ((on_face _ _).mpr members.2.1) ((on_face _ _).mpr members.2.2) hx
      ((on_face _ _).mpr aL) ((on_face _ _).mpr bL) (fun h => cL ((on_face _ _).mp h))
      ((on_face _ _).mpr aR) ((on_face _ _).mpr cR) (fun h => bR ((on_face _ _).mp h)) noncollinear
  obtain ⟨hc, hl, hr⟩ := net.fan_positions prism_kind q k
  refine ⟨t, u, ht, hu, ?_⟩
  change net.place (fanFace q k) x - net.place (fanFace q 1) (graph.prismVertex (fanCenter q)) =
    t • (net.fanRays q k.castSucc - net.place (fanFace q 1) (graph.prismVertex (fanCenter q))) +
    u • (net.fanRays q k.succ - net.place (fanFace q 1) (graph.prismVertex (fanCenter q)))
  rw [hc, hl, hr]
  have mapped := congrArg (net.place (fanFace q k)).linear coords
  have difference (v w : Space) : (net.place (fanFace q k)).linear (v - w) =
      net.place (fanFace q k) v - net.place (fanFace q k) w :=
    (net.place (fanFace q k)).linearMap_vsub v w
  simpa only [map_add, map_smul, difference] using mapped

/-- Every pair in either uncut four-face fan is separated, including its whole quadrilateral. -/
theorem PrismFallbackDevelopment.vertexFan_nonoverlap (q : Fin 2) (i j : Fin 4) (different : i ≠ j) :
    Disjoint (interior (net.place (fanFace q i) '' (graph.prismDiagonalFace small_faces (fanFace q i)).val))
      (interior (net.place (fanFace q j) '' (graph.prismDiagonalFace small_faces (fanFace q j)).val)) :=
  ((net.vertexFan prism_kind q).cornerCone_nonoverlap (net.vertexFan_one_turn prism_kind q) i j different).mono
    (interior_mono (net.face_subset_vertexFan_cone prism_kind q i))
    (interior_mono (net.face_subset_vertexFan_cone prism_kind q j))

/-- Twelve of the fifteen fallback comparisons are now supplied; three explicit pairs remain. -/
theorem PrismFallbackDevelopment.hasEdgeUnfolding_of_three_pairs
    (core_safe : ∀ f ∈ starCore, ∀ g ∈ starCore, f ≠ g →
      Disjoint (interior (net.place f '' (graph.prismDiagonalFace small_faces f).val))
        (interior (net.place g '' (graph.prismDiagonalFace small_faces g).val)))
    (remaining : ∀ f g, s(f, g) ∈ fallbackHardPairs →
      Disjoint (interior (net.place f '' (graph.prismDiagonalFace small_faces f).val))
        (interior (net.place g '' (graph.prismDiagonalFace small_faces g).val))) : P.HasEdgeUnfolding := by
  apply net.hasEdgeUnfolding_of_star_core prism_kind core_safe
  intro f g pair
  rcases (by decide : ∀ f g, s(f, g) ∈ fallbackRemainingPairs →
    s(f, g) ∈ fallbackHardPairs ∨ ∃ (q : Fin 2) (i j : Fin 4),
      i ≠ j ∧ f = fanFace q i ∧ g = fanFace q j) f g pair with hard | fan
  · exact remaining f g hard
  · obtain ⟨q, i, j, distinct, rfl, rfl⟩ := fan
    exact net.vertexFan_nonoverlap prism_kind q i j distinct

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
