import SixVertexUnfolding.Geometry.OctahedralJunctionAngles
import SixVertexUnfolding.Geometry.OctahedralNetPlacement

/-! The junction chains settle nine more pairs of actual developed subdivision triangles. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open OctahedralTriangles OctahedralNet

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- One of the eight actual closed triangles in the constructed planar development. -/
def placedTriangle (index : FaceIndex) : Set Plane :=
  net.place index '' graph.triangle (OctahedralNet.triangle source slit index)

/-- The four triangle indices around an uncut equator junction, in cyclic order. -/
def junctionIndex (i : Fin 3) : Fin 4 → FaceIndex :=
  ![(true, i.castSucc), (false, i.castSucc), (false, i.succ), (true, i.succ)]

theorem junction_triangle (i : Fin 3) (k : Fin 4) :
    (net.junctionChain i).triangle k = net.placedTriangle (junctionIndex i k) := by
  fin_cases k
  · change convexHull ℝ ({(net.patch i.castSucc).right, (net.patch i.castSucc).apex, (net.patch i.castSucc).left} : Set Plane) =
      net.petal i.castSucc '' graph.triangle (fanTriangle source (slit + i.castSucc))
    rw [net.petal_triangle]
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · change convexHull ℝ ({(net.patch i.castSucc).right, (net.patch i.castSucc).left, (net.patch i.castSucc).pole} : Set Plane) =
      net.fan.place i.castSucc '' graph.triangle (fanTriangle (opposite source) (slit + i.castSucc))
    rw [net.fan_triangle]
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · change convexHull ℝ ({(net.patch i.castSucc).right, (net.patch i.castSucc).pole, (net.patch i.succ).right} : Set Plane) =
      net.fan.place i.succ '' graph.triangle (fanTriangle (opposite source) (slit + i.succ))
    rw [net.fan_triangle, net.consecutive_patch_corner, net.patch_pole, net.patch_pole]
    congr 1
    exact Set.insert_comm _ _ _
  · change convexHull ℝ ({(net.patch i.castSucc).right, (net.patch i.succ).right, (net.patch i.succ).apex} : Set Plane) =
      net.petal i.succ '' graph.triangle (fanTriangle source (slit + i.succ))
    rw [net.petal_triangle, net.consecutive_patch_corner]
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

/-- Two indexed triangles are safe when their planar interiors are disjoint. -/
def Separated (a b : FaceIndex) : Prop :=
  Disjoint (interior (net.placedTriangle a)) (interior (net.placedTriangle b))

theorem Separated.symm {a b : FaceIndex} (safe : net.Separated a b) : net.Separated b a := Disjoint.symm safe

theorem junction_separated (i : Fin 3) (j k : Fin 4) (different : j ≠ k) :
    net.Separated (junctionIndex i j) (junctionIndex i k) := by
  have safe := net.junction_nonoverlap i j k different
  rw [net.junction_triangle, net.junction_triangle] at safe
  exact safe

theorem neighboring_fan_petal (i : Fin 3) : net.Separated (false, i.castSucc) (true, i.succ) :=
  net.junction_separated i 1 3 (by decide)

theorem neighboring_petal_fan (i : Fin 3) : net.Separated (true, i.castSucc) (false, i.succ) :=
  net.junction_separated i 0 2 (by decide)

theorem neighboring_petals (i : Fin 3) : net.Separated (true, i.castSucc) (true, i.succ) :=
  net.junction_separated i 0 3 (by decide)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
