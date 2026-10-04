import SixVertexUnfolding.Geometry.PrismDiagonalUpperCaseB
import SixVertexUnfolding.Geometry.PrismDiagonalCornerCones

/-! The two cap views use the same three-face and four-face fans. The upper
view reads them backwards, with base 4--3 and the two quadrilaterals exchanged. -/

namespace SixVertexUnfolding.Prism

open FaceLabel

def capFace : Fin 2 → FaceLabel := ![A, F]
def capLeftFace : Fin 2 → FaceLabel := ![B, D]
def capRightFace : Fin 2 → FaceLabel := ![D, B]
def capLeftVertex : Fin 2 → Fin 6 := ![0, 4]
def capRightVertex : Fin 2 → Fin 6 := ![1, 3]
def capSource : Fin 2 → Fin 6 := ![2, 5]
def capOtherSource : Fin 2 → Fin 6 := ![5, 2]
def capLeftWitness : Fin 2 → Fin 6 := ![3, 1]
def capRightWitness : Fin 2 → Fin 6 := ![4, 0]

end SixVertexUnfolding.Prism

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel EuclideanGeometry Real

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4}
variable (prism_kind : graph.kind = .prismDiagonal)
variable (net : graph.PrismFallbackDevelopment small_faces)

noncomputable def PrismFallbackDevelopment.capLeftFan (q : Fin 2) : ThreeTriangleChain :=
  ![net.shortVertexFan prism_kind 0, (net.shortVertexFan prism_kind 1).reverse] q

noncomputable def PrismFallbackDevelopment.capRightFan (q : Fin 2) : FourTriangleChain :=
  ![net.vertexFan prism_kind 0, (net.vertexFan prism_kind 1).reverse] q

include prism_kind

/-- Both pairs of actual fans share precisely the first cap triangle. -/
theorem PrismFallbackDevelopment.cap_shared_triangle (q : Fin 2) :
    (net.capRightFan prism_kind q).center = (net.capLeftFan prism_kind q).ray 1 ∧
    (net.capRightFan prism_kind q).ray 0 = (net.capLeftFan prism_kind q).ray 0 ∧
    (net.capRightFan prism_kind q).ray 1 = (net.capLeftFan prism_kind q).center := by
  fin_cases q
  · exact ⟨(net.fan_positions prism_kind 0 0).1, rfl, (net.short_fan_positions prism_kind 0 0).1.symm⟩
  · exact ⟨(net.fan_positions prism_kind 1 2).1, rfl, rfl⟩

/-- The three rays used at the left quadrilateral are its actual original vertices. -/
theorem PrismFallbackDevelopment.cap_left_positions (q : Fin 2) :
    (net.capLeftFan prism_kind q).center = net.place (capLeftFace q) (graph.prismVertex (capLeftVertex q)) ∧
    (net.capLeftFan prism_kind q).ray 3 = net.place (capLeftFace q) (graph.prismVertex (capSource q)) ∧
    (net.capLeftFan prism_kind q).ray 2 = net.place (capLeftFace q) (graph.prismVertex (capLeftWitness q)) ∧
    (net.capLeftFan prism_kind q).center = net.place (capFace q) (graph.prismVertex (capLeftVertex q)) ∧
    (net.capLeftFan prism_kind q).ray 0 = net.place (capFace q) (graph.prismVertex (capSource q)) := by
  fin_cases q
  · exact ⟨(net.short_fan_positions prism_kind 0 2).1, rfl,
      (net.short_fan_positions prism_kind 0 2).2.1, (net.short_fan_positions prism_kind 0 0).1, rfl⟩
  · exact ⟨(net.short_fan_positions prism_kind 1 0).1, rfl, rfl,
      (net.short_fan_positions prism_kind 1 2).1, rfl⟩

/-- The corresponding data on the right quadrilateral. -/
theorem PrismFallbackDevelopment.cap_right_positions (q : Fin 2) :
    (net.capRightFan prism_kind q).center = net.place (capRightFace q) (graph.prismVertex (capRightVertex q)) ∧
    (net.capRightFan prism_kind q).ray 4 = net.place (capRightFace q) (graph.prismVertex (capSource q)) ∧
    (net.capRightFan prism_kind q).ray 3 = net.place (capRightFace q) (graph.prismVertex (capRightWitness q)) ∧
    (net.capRightFan prism_kind q).center = net.place (capFace q) (graph.prismVertex (capRightVertex q)) ∧
    (net.capRightFan prism_kind q).ray 0 = net.place (capFace q) (graph.prismVertex (capSource q)) := by
  fin_cases q
  · exact ⟨(net.fan_positions prism_kind 0 3).1, rfl,
      (net.fan_positions prism_kind 0 3).2.1, (net.fan_positions prism_kind 0 0).1, rfl⟩
  · exact ⟨(net.fan_positions prism_kind 1 0).1, rfl, rfl,
      (net.fan_positions prism_kind 1 3).1, rfl⟩

/-- Cutting duplicates an original edge without changing its length. -/
theorem PrismFallbackDevelopment.cap_copied_lengths (q : Fin 2) :
    (net.capLeftFan prism_kind q).radius 3 = (net.capLeftFan prism_kind q).radius 0 ∧
    (net.capRightFan prism_kind q).radius 4 = (net.capRightFan prism_kind q).radius 0 := by
  have rigid (f : FaceLabel) (i j : Fin 6) (hi : i ∈ faceVertices f) (hj : j ∈ faceVertices f) :=
    net.rigid f _ ((graph.prismVertex_mem_face small_faces prism_kind f i).mpr hi)
      _ ((graph.prismVertex_mem_face small_faces prism_kind f j).mpr hj)
  obtain ⟨lc, lp, _, la, lm⟩ := net.cap_left_positions prism_kind q
  obtain ⟨rc, rp, _, ra, rm⟩ := net.cap_right_positions prism_kind q
  constructor
  · change dist _ _ = dist _ _
    rw [lp, lm]
    calc
      _ = dist (graph.prismVertex (capLeftVertex q) : Space) (graph.prismVertex (capSource q)) := by
        rw [lc]; exact rigid _ _ _ (by fin_cases q <;> decide) (by fin_cases q <;> decide)
      _ = _ := by rw [la]; exact (rigid _ _ _ (by fin_cases q <;> decide) (by fin_cases q <;> decide)).symm
  · change dist _ _ = dist _ _
    rw [rp, rm]
    calc
      _ = dist (graph.prismVertex (capRightVertex q) : Space) (graph.prismVertex (capSource q)) := by
        rw [rc]; exact rigid _ _ _ (by fin_cases q <;> decide) (by fin_cases q <;> decide)
      _ = _ := by rw [ra]; exact (rigid _ _ _ (by fin_cases q <;> decide) (by fin_cases q <;> decide)).symm

/-- Positive curvature bounds the total turn of both cap fans. -/
theorem PrismFallbackDevelopment.cap_one_turn (q : Fin 2) :
    (∑ i, (net.capLeftFan prism_kind q).corner i) < 2 * π ∧
    (∑ i, (net.capRightFan prism_kind q).corner i) < 2 * π := by
  fin_cases q
  · exact ⟨net.shortVertexFan_one_turn prism_kind 0, net.vertexFan_one_turn prism_kind 0⟩
  · change (∑ i, (net.shortVertexFan prism_kind 1).reverse.corner i) < 2 * π ∧
      (∑ i, (net.vertexFan prism_kind 1).reverse.corner i) < 2 * π
    rw [ThreeTriangleChain.reverse_angle_sum, FourTriangleChain.reverse_angle_sum]
    exact ⟨net.shortVertexFan_one_turn prism_kind 1, net.vertexFan_one_turn prism_kind 1⟩

/-- The cut-ray directions are the cap's base angles plus the actual curvatures. -/
theorem PrismFallbackDevelopment.cap_directions (q : Fin 2) :
    (graph.prismAngle small_faces (capFace q) (capLeftVertex q) + graph.curvature (vertexLabel (capLeftVertex q))) +
      (net.capLeftFan prism_kind q).corner 1 + (net.capLeftFan prism_kind q).corner 2 = 2 * π ∧
    (graph.prismAngle small_faces (capFace q) (capRightVertex q) + graph.curvature (vertexLabel (capRightVertex q))) +
      (net.capRightFan prism_kind q).corner 1 + (net.capRightFan prism_kind q).corner 2 +
        (net.capRightFan prism_kind q).corner 3 = 2 * π := by
  fin_cases q
  · have h := graph.prism_lower_base_angles (small_faces := small_faces) prism_kind
    simp [capLeftFan, capRightFan, capFace, capLeftVertex, capRightVertex,
      net.shortVertexFan_corner prism_kind, net.vertexFan_corner prism_kind,
      shortFanFace, shortFanCenter, fanFace, fanCenter]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · have h := graph.prism_upper_base_angles (small_faces := small_faces) prism_kind
    simp [capLeftFan, capRightFan, capFace, capLeftVertex, capRightVertex,
      net.shortVertexFan_corner prism_kind, net.vertexFan_corner prism_kind,
      shortFanFace, shortFanCenter, fanFace, fanCenter, Fin.rev]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
