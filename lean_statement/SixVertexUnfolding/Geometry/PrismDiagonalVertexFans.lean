import SixVertexUnfolding.Geometry.PrismDiagonalStarFallback
import SixVertexUnfolding.Geometry.PrismDiagonalAngleSums
import SixVertexUnfolding.Geometry.FourCornerCones
import SixVertexUnfolding.Geometry.FaceCornerCones

/-! The two four-face fans at uncut vertices 1 and 3. Whole quadrilaterals
stay inside their corner cones, so positive curvature separates every pair. -/

namespace SixVertexUnfolding.Prism

open FaceLabel

def fanCenter : Fin 2 → Fin 6 := ![1, 3]
def fanFace : Fin 2 → Fin 4 → FaceLabel := ![![A, C, E, D], ![B, C, E, F]]
def fanRayLabel : Fin 2 → Fin 5 → Fin 6 := ![![2, 0, 3, 4, 2], ![5, 0, 1, 4, 5]]

end SixVertexUnfolding.Prism

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel EuclideanGeometry Real

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4}
variable (prism_kind : graph.kind = .prismDiagonal)
variable (net : graph.PrismFallbackDevelopment small_faces)

private theorem fan_members (q : Fin 2) (k : Fin 4) :
    fanCenter q ∈ faceVertices (fanFace q k) ∧
    fanRayLabel q k.castSucc ∈ faceVertices (fanFace q k) ∧
    fanRayLabel q k.succ ∈ faceVertices (fanFace q k) := by revert q k; decide

private theorem fan_distinct (q : Fin 2) (k : Fin 4) :
    fanCenter q ≠ fanRayLabel q k.castSucc ∧ fanCenter q ≠ fanRayLabel q k.succ ∧
    fanRayLabel q k.castSucc ≠ fanRayLabel q k.succ := by revert q k; decide

include prism_kind in
private theorem fan_on_face (q : Fin 2) (k : Fin 4) :
    (graph.prismVertex (fanCenter q) : Space) ∈ (graph.prismDiagonalFace small_faces (fanFace q k)).val ∧
    (graph.prismVertex (fanRayLabel q k.castSucc) : Space) ∈ (graph.prismDiagonalFace small_faces (fanFace q k)).val ∧
    (graph.prismVertex (fanRayLabel q k.succ) : Space) ∈ (graph.prismDiagonalFace small_faces (fanFace q k)).val := by
  simp only [graph.prismVertex_mem_face small_faces prism_kind]
  exact fan_members q k

/-- Five successive edge rays, keeping the two copies of the cut endpoint distinct. -/
noncomputable def PrismFallbackDevelopment.fanRays (q : Fin 2) : Fin 5 → Plane :=
  ![net.place (fanFace q 0) (graph.prismVertex (fanRayLabel q 0)),
    net.place (fanFace q 0) (graph.prismVertex (fanRayLabel q 1)),
    net.place (fanFace q 1) (graph.prismVertex (fanRayLabel q 2)),
    net.place (fanFace q 2) (graph.prismVertex (fanRayLabel q 3)),
    net.place (fanFace q 3) (graph.prismVertex (fanRayLabel q 4))]

include prism_kind in
/-- Successive placements use the same actual vertex on every retained hinge. -/
theorem PrismFallbackDevelopment.fan_positions (q : Fin 2) (k : Fin 4) :
    net.place (fanFace q 1) (graph.prismVertex (fanCenter q)) =
      net.place (fanFace q k) (graph.prismVertex (fanCenter q)) ∧
    net.fanRays q k.castSucc = net.place (fanFace q k) (graph.prismVertex (fanRayLabel q k.castSucc)) ∧
    net.fanRays q k.succ = net.place (fanFace q k) (graph.prismVertex (fanRayLabel q k.succ)) := by
  have shared (j : Fin 3) (i : Fin 6)
      (first : i ∈ faceVertices (fanFace q j.castSucc))
      (second : i ∈ faceVertices (fanFace q j.succ)) :
      net.place (fanFace q j.castSucc) (graph.prismVertex i) =
        net.place (fanFace q j.succ) (graph.prismVertex i) :=
    net.joined_on_hinge _ _ ((by decide : ∀ q j, fallbackHinges.Adj
      (fanFace q j.castSucc) (fanFace q j.succ)) q j)
      ⟨(graph.prismVertex_mem_face small_faces prism_kind _ _).mpr first,
        (graph.prismVertex_mem_face small_faces prism_kind _ _).mpr second⟩
  have center (j : Fin 3) := shared j (fanCenter q)
    (fan_members q j.castSucc).1 (fan_members q j.succ).1
  have ray (j : Fin 3) := shared j (fanRayLabel q j.succ.castSucc)
    (fan_members q j.castSucc).2.2 (fan_members q j.succ).2.1
  fin_cases k
  · exact ⟨(center 0).symm, rfl, rfl⟩
  · exact ⟨rfl, ray 0, rfl⟩
  · exact ⟨center 1, ray 1, rfl⟩
  · exact ⟨(center 1).trans (center 2), ray 2, rfl⟩

/-- The actual four whole-face corners form an outward chain. -/
noncomputable def PrismFallbackDevelopment.vertexFan (q : Fin 2) : FourTriangleChain where
  center := net.place (fanFace q 1) (graph.prismVertex (fanCenter q))
  ray := net.fanRays q
  noncollinear := by
    intro k
    obtain ⟨hc, hl, hr⟩ := net.fan_positions prism_kind q k
    rw [hc, hl, hr]
    have member := fan_on_face (graph := graph) (small_faces := small_faces) prism_kind q k
    have distinct := fan_distinct q k
    apply P.placed_triangle_noncollinear (graph.prismVertex (fanCenter q))
      (graph.prismVertex (fanRayLabel q k.castSucc)) (graph.prismVertex (fanRayLabel q k.succ))
      (graph.vertex.injective.ne (vertexLabel.injective.ne distinct.1))
      (graph.vertex.injective.ne (vertexLabel.injective.ne distinct.2.1))
      (graph.vertex.injective.ne (vertexLabel.injective.ne distinct.2.2))
    exacts [net.rigid _ _ member.1 _ member.2.1,
      net.rigid _ _ member.1 _ member.2.2, net.rigid _ _ member.2.1 _ member.2.2]
  outward := by
    intro k
    have first := net.fan_positions prism_kind q k.castSucc
    have second := net.fan_positions prism_kind q k.succ
    have first_mem := fan_on_face (graph := graph) (small_faces := small_faces) prism_kind q k.castSucc
    have second_mem := fan_on_face (graph := graph) (small_faces := small_faces) prism_kind q k.succ
    have adjacent := (by decide : ∀ q k, fallbackHinges.Adj
      (fanFace q k.castSucc) (fanFace q k.succ)) q k
    rw [first.1, show k.succ.castSucc = k.castSucc.succ from rfl, first.2.2,
      first.2.1, second.2.2]
    exact (graph.prismDiagonalFace small_faces (fanFace q k.castSucc)).opposite_sides_of_nonoverlap
      (graph.prismDiagonalFace small_faces (fanFace q k.succ)) _ _ (net.rigid _) (net.rigid _)
      (net.joined_on_hinge _ _ adjacent) (net.hinge_nonoverlap _ _ adjacent)
      _ ⟨⟨first_mem.1, second_mem.1⟩, (graph.prismVertex _).property⟩
      _ ⟨⟨first_mem.2.2, second_mem.2.1⟩, (graph.prismVertex _).property⟩
      (graph.prismVertex_injective.ne (fan_distinct q k.castSucc).2.1)
      _ first_mem.2.1 _ second_mem.2.2

/-- Each developed corner is the full original face angle, also for a quadrilateral. -/
theorem PrismFallbackDevelopment.vertexFan_corner (q : Fin 2) (k : Fin 4) :
    (net.vertexFan prism_kind q).corner k = graph.prismAngle small_faces (fanFace q k) (fanCenter q) := by
  change angle (net.fanRays q k.castSucc) (net.place (fanFace q 1) (graph.prismVertex (fanCenter q)))
    (net.fanRays q k.succ) = _
  obtain ⟨hc, hl, hr⟩ := net.fan_positions prism_kind q k
  rw [hc, hl, hr]
  have member := fan_on_face (graph := graph) (small_faces := small_faces) prism_kind q k
  rw [triangle_angle_of_distances _ _ _ _ _ _
    (net.rigid _ _ member.1 _ member.2.1) (net.rigid _ _ member.1 _ member.2.2)
    (net.rigid _ _ member.2.1 _ member.2.2)]
  rw [graph.prismAngle_eq small_faces prism_kind, if_pos (fan_members q k).1]
  fin_cases q <;> fin_cases k <;> simp [fanCenter, fanFace, fanRayLabel, neighbors, angle_comm]

/-- Positive curvature supplies the one-turn bound for both actual vertex fans. -/
theorem PrismFallbackDevelopment.vertexFan_one_turn (q : Fin 2) :
    (∑ k : Fin 4, (net.vertexFan prism_kind q).corner k) < 2 * π := by
  have total := graph.prismAngle_total small_faces prism_kind (fanCenter q)
  have bound := graph.totalAngleAt_lt_two_pi small_faces (vertexLabel (fanCenter q))
  simp only [net.vertexFan_corner prism_kind, Fin.sum_univ_four] at ⊢
  rw [sum_faces] at total
  fin_cases q <;>
    simp [fanCenter, fanFace, graph.prismAngle_zero small_faces prism_kind, faceVertices] at total bound ⊢ <;>
    linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
