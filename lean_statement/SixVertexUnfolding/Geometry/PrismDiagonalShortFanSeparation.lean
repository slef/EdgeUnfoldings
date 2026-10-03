import SixVertexUnfolding.Geometry.PrismDiagonalShortVertexFans

/-! Separation of whole faces in the shorter fans at vertices 0 and 4. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4}
variable (prism_kind : graph.kind = .prismDiagonal)
variable (net : graph.PrismFallbackDevelopment small_faces)
include prism_kind

/-- Every point of each whole polygon lies inside its actual corner cone. -/
theorem PrismFallbackDevelopment.face_subset_shortVertexFan_cone (q : Fin 2) (k : Fin 3) :
    net.place (shortFanFace q k) '' (graph.prismDiagonalFace small_faces (shortFanFace q k)).val ⊆
      (net.shortVertexFan prism_kind q).cornerCone k := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨l, r, aL, bL, cL, aR, cR, bR⟩ := (by decide : ∀ q k,
    ∃ l r : FaceLabel,
      shortFanCenter q ∈ faceVertices l ∧ shortFanRayLabel q k.castSucc ∈ faceVertices l ∧
      shortFanRayLabel q k.succ ∉ faceVertices l ∧
      shortFanCenter q ∈ faceVertices r ∧ shortFanRayLabel q k.succ ∈ faceVertices r ∧
      shortFanRayLabel q k.castSucc ∉ faceVertices r) q k
  have members := (by decide : ∀ q k,
    shortFanCenter q ∈ faceVertices (shortFanFace q k) ∧
    shortFanRayLabel q k.castSucc ∈ faceVertices (shortFanFace q k) ∧
    shortFanRayLabel q k.succ ∈ faceVertices (shortFanFace q k)) q k
  have distinct := (by decide : ∀ q k,
    shortFanCenter q ≠ shortFanRayLabel q k.castSucc ∧ shortFanCenter q ≠ shortFanRayLabel q k.succ ∧
    shortFanRayLabel q k.castSucc ≠ shortFanRayLabel q k.succ) q k
  have on_face (f : FaceLabel) (i : Fin 6) := graph.prismVertex_mem_face small_faces prism_kind f i
  have noncollinear := P.no_three_collinear_vertices
    (graph.prismVertex (shortFanCenter q)).property (graph.prismVertex (shortFanRayLabel q k.castSucc)).property
    (graph.prismVertex (shortFanRayLabel q k.succ)).property
    (graph.prismVertex_injective.ne distinct.1) (graph.prismVertex_injective.ne distinct.2.1)
    (graph.prismVertex_injective.ne distinct.2.2)
  obtain ⟨t, u, ht, hu, coords⟩ :=
    (graph.prismDiagonalFace small_faces (shortFanFace q k)).nonnegative_corner_coordinates_of_facets
      (graph.prismDiagonalFace small_faces l) (graph.prismDiagonalFace small_faces r)
      (graph.prismVertex (shortFanCenter q)) (graph.prismVertex (shortFanRayLabel q k.castSucc))
      (graph.prismVertex (shortFanRayLabel q k.succ)) x
      ((on_face _ _).mpr members.1) ((on_face _ _).mpr members.2.1) ((on_face _ _).mpr members.2.2) hx
      ((on_face _ _).mpr aL) ((on_face _ _).mpr bL) (fun h => cL ((on_face _ _).mp h))
      ((on_face _ _).mpr aR) ((on_face _ _).mpr cR) (fun h => bR ((on_face _ _).mp h)) noncollinear
  obtain ⟨hc, hl, hr⟩ := net.short_fan_positions prism_kind q k
  refine ⟨t, u, ht, hu, ?_⟩
  change net.place (shortFanFace q k) x - net.place (shortFanFace q 1) (graph.prismVertex (shortFanCenter q)) =
    t • (net.shortFanRays q k.castSucc - net.place (shortFanFace q 1) (graph.prismVertex (shortFanCenter q))) +
    u • (net.shortFanRays q k.succ - net.place (shortFanFace q 1) (graph.prismVertex (shortFanCenter q)))
  rw [hc, hl, hr]
  have mapped := congrArg (net.place (shortFanFace q k)).linear coords
  have difference (v w : Space) : (net.place (shortFanFace q k)).linear (v - w) =
      net.place (shortFanFace q k) v - net.place (shortFanFace q k) w :=
    (net.place (shortFanFace q k)).linearMap_vsub v w
  simpa only [map_add, map_smul, difference] using mapped

/-- Every pair in either uncut three-face fan is separated, including its whole quadrilateral. -/
theorem PrismFallbackDevelopment.shortVertexFan_nonoverlap (q : Fin 2) (i j : Fin 3) (different : i ≠ j) :
    Disjoint (interior (net.place (shortFanFace q i) '' (graph.prismDiagonalFace small_faces (shortFanFace q i)).val))
      (interior (net.place (shortFanFace q j) '' (graph.prismDiagonalFace small_faces (shortFanFace q j)).val)) :=
  ((net.shortVertexFan prism_kind q).cornerCone_nonoverlap (net.shortVertexFan_one_turn prism_kind q) i j different).mono
    (interior_mono (net.face_subset_shortVertexFan_cone prism_kind q i))
    (interior_mono (net.face_subset_shortVertexFan_cone prism_kind q j))

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
