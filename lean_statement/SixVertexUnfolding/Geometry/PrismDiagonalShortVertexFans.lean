import SixVertexUnfolding.Geometry.PrismDiagonalStarFallback
import SixVertexUnfolding.Geometry.PrismDiagonalAngleSums
import SixVertexUnfolding.Geometry.ThreeCornerCones
import SixVertexUnfolding.Geometry.FaceCornerCones

/-! The two three-face fans at uncut vertices 0 and 4. Whole quadrilaterals
stay inside their corner cones, so positive curvature separates every pair. -/

namespace SixVertexUnfolding.Prism

open FaceLabel

def shortFanCenter : Fin 2 → Fin 6 := ![0, 4]
def shortFanFace : Fin 2 → Fin 3 → FaceLabel := ![![A, C, B], ![D, E, F]]
def shortFanRayLabel : Fin 2 → Fin 4 → Fin 6 := ![![2, 1, 3, 2], ![5, 1, 3, 5]]

end SixVertexUnfolding.Prism

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel EuclideanGeometry Real

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4}
variable (prism_kind : graph.kind = .prismDiagonal)
variable (net : graph.PrismFallbackDevelopment small_faces)

private theorem short_fan_members (q : Fin 2) (k : Fin 3) :
    shortFanCenter q ∈ faceVertices (shortFanFace q k) ∧
    shortFanRayLabel q k.castSucc ∈ faceVertices (shortFanFace q k) ∧
    shortFanRayLabel q k.succ ∈ faceVertices (shortFanFace q k) := by revert q k; decide

private theorem short_fan_distinct (q : Fin 2) (k : Fin 3) :
    shortFanCenter q ≠ shortFanRayLabel q k.castSucc ∧ shortFanCenter q ≠ shortFanRayLabel q k.succ ∧
    shortFanRayLabel q k.castSucc ≠ shortFanRayLabel q k.succ := by revert q k; decide

include prism_kind in
private theorem short_fan_on_face (q : Fin 2) (k : Fin 3) :
    (graph.prismVertex (shortFanCenter q) : Space) ∈ (graph.prismDiagonalFace small_faces (shortFanFace q k)).val ∧
    (graph.prismVertex (shortFanRayLabel q k.castSucc) : Space) ∈ (graph.prismDiagonalFace small_faces (shortFanFace q k)).val ∧
    (graph.prismVertex (shortFanRayLabel q k.succ) : Space) ∈ (graph.prismDiagonalFace small_faces (shortFanFace q k)).val := by
  simp only [graph.prismVertex_mem_face small_faces prism_kind]
  exact short_fan_members q k

/-- Four successive edge rays, keeping the two copies of the cut endpoint distinct. -/
noncomputable def PrismFallbackDevelopment.shortFanRays (q : Fin 2) : Fin 4 → Plane :=
  ![net.place (shortFanFace q 0) (graph.prismVertex (shortFanRayLabel q 0)),
    net.place (shortFanFace q 0) (graph.prismVertex (shortFanRayLabel q 1)),
    net.place (shortFanFace q 1) (graph.prismVertex (shortFanRayLabel q 2)),
    net.place (shortFanFace q 2) (graph.prismVertex (shortFanRayLabel q 3))]

include prism_kind in
/-- Successive placements use the same actual vertex on every retained hinge. -/
theorem PrismFallbackDevelopment.short_fan_positions (q : Fin 2) (k : Fin 3) :
    net.place (shortFanFace q 1) (graph.prismVertex (shortFanCenter q)) =
      net.place (shortFanFace q k) (graph.prismVertex (shortFanCenter q)) ∧
    net.shortFanRays q k.castSucc = net.place (shortFanFace q k) (graph.prismVertex (shortFanRayLabel q k.castSucc)) ∧
    net.shortFanRays q k.succ = net.place (shortFanFace q k) (graph.prismVertex (shortFanRayLabel q k.succ)) := by
  have shared (j : Fin 2) (i : Fin 6)
      (first : i ∈ faceVertices (shortFanFace q j.castSucc))
      (second : i ∈ faceVertices (shortFanFace q j.succ)) :
      net.place (shortFanFace q j.castSucc) (graph.prismVertex i) =
        net.place (shortFanFace q j.succ) (graph.prismVertex i) :=
    net.joined_on_hinge _ _ ((by decide : ∀ q j, fallbackHinges.Adj
      (shortFanFace q j.castSucc) (shortFanFace q j.succ)) q j)
      ⟨(graph.prismVertex_mem_face small_faces prism_kind _ _).mpr first,
        (graph.prismVertex_mem_face small_faces prism_kind _ _).mpr second⟩
  have center (j : Fin 2) := shared j (shortFanCenter q)
    (short_fan_members q j.castSucc).1 (short_fan_members q j.succ).1
  have ray (j : Fin 2) := shared j (shortFanRayLabel q j.succ.castSucc)
    (short_fan_members q j.castSucc).2.2 (short_fan_members q j.succ).2.1
  fin_cases k
  · exact ⟨(center 0).symm, rfl, rfl⟩
  · exact ⟨rfl, ray 0, rfl⟩
  · exact ⟨center 1, ray 1, rfl⟩

/-- The actual three whole-face corners form an outward chain. -/
noncomputable def PrismFallbackDevelopment.shortVertexFan (q : Fin 2) : ThreeTriangleChain where
  center := net.place (shortFanFace q 1) (graph.prismVertex (shortFanCenter q))
  ray := net.shortFanRays q
  noncollinear := by
    intro k
    obtain ⟨hc, hl, hr⟩ := net.short_fan_positions prism_kind q k
    rw [hc, hl, hr]
    have member := short_fan_on_face (graph := graph) (small_faces := small_faces) prism_kind q k
    have distinct := short_fan_distinct q k
    apply P.placed_triangle_noncollinear (graph.prismVertex (shortFanCenter q))
      (graph.prismVertex (shortFanRayLabel q k.castSucc)) (graph.prismVertex (shortFanRayLabel q k.succ))
      (graph.vertex.injective.ne (vertexLabel.injective.ne distinct.1))
      (graph.vertex.injective.ne (vertexLabel.injective.ne distinct.2.1))
      (graph.vertex.injective.ne (vertexLabel.injective.ne distinct.2.2))
    exacts [net.rigid _ _ member.1 _ member.2.1,
      net.rigid _ _ member.1 _ member.2.2, net.rigid _ _ member.2.1 _ member.2.2]
  outward := by
    intro k
    have first := net.short_fan_positions prism_kind q k.castSucc
    have second := net.short_fan_positions prism_kind q k.succ
    have first_mem := short_fan_on_face (graph := graph) (small_faces := small_faces) prism_kind q k.castSucc
    have second_mem := short_fan_on_face (graph := graph) (small_faces := small_faces) prism_kind q k.succ
    have adjacent := (by decide : ∀ q k, fallbackHinges.Adj
      (shortFanFace q k.castSucc) (shortFanFace q k.succ)) q k
    rw [first.1, show k.succ.castSucc = k.castSucc.succ from rfl, first.2.2,
      first.2.1, second.2.2]
    exact (graph.prismDiagonalFace small_faces (shortFanFace q k.castSucc)).opposite_sides_of_nonoverlap
      (graph.prismDiagonalFace small_faces (shortFanFace q k.succ)) _ _ (net.rigid _) (net.rigid _)
      (net.joined_on_hinge _ _ adjacent) (net.hinge_nonoverlap _ _ adjacent)
      _ ⟨⟨first_mem.1, second_mem.1⟩, (graph.prismVertex _).property⟩
      _ ⟨⟨first_mem.2.2, second_mem.2.1⟩, (graph.prismVertex _).property⟩
      (graph.prismVertex_injective.ne (short_fan_distinct q k.castSucc).2.1)
      _ first_mem.2.1 _ second_mem.2.2

/-- Each developed corner is the full original face angle, also for a quadrilateral. -/
theorem PrismFallbackDevelopment.shortVertexFan_corner (q : Fin 2) (k : Fin 3) :
    (net.shortVertexFan prism_kind q).corner k = graph.prismAngle small_faces (shortFanFace q k) (shortFanCenter q) := by
  change angle (net.shortFanRays q k.castSucc) (net.place (shortFanFace q 1) (graph.prismVertex (shortFanCenter q)))
    (net.shortFanRays q k.succ) = _
  obtain ⟨hc, hl, hr⟩ := net.short_fan_positions prism_kind q k
  rw [hc, hl, hr]
  have member := short_fan_on_face (graph := graph) (small_faces := small_faces) prism_kind q k
  rw [triangle_angle_of_distances _ _ _ _ _ _
    (net.rigid _ _ member.1 _ member.2.1) (net.rigid _ _ member.1 _ member.2.2)
    (net.rigid _ _ member.2.1 _ member.2.2)]
  rw [graph.prismAngle_eq small_faces prism_kind, if_pos (short_fan_members q k).1]
  fin_cases q <;> fin_cases k <;> simp [shortFanCenter, shortFanFace, shortFanRayLabel, neighbors, angle_comm]

/-- Positive curvature supplies the one-turn bound for both actual vertex fans. -/
theorem PrismFallbackDevelopment.shortVertexFan_one_turn (q : Fin 2) :
    (∑ k : Fin 3, (net.shortVertexFan prism_kind q).corner k) < 2 * π := by
  have total := graph.prismAngle_total small_faces prism_kind (shortFanCenter q)
  have bound := graph.totalAngleAt_lt_two_pi small_faces (vertexLabel (shortFanCenter q))
  simp only [net.shortVertexFan_corner prism_kind, Fin.sum_univ_three] at ⊢
  rw [sum_faces] at total
  fin_cases q <;>
    simp [shortFanCenter, shortFanFace, graph.prismAngle_zero small_faces prism_kind, faceVertices] at total bound ⊢ <;>
    linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
