import SixVertexUnfolding.Geometry.OctahedralSectorIntersections
import SixVertexUnfolding.Geometry.OctahedralVertexNeighborhood
import Mathlib.Analysis.Normed.Group.AddCircle

/-! The actual punctured vertex fan has an angular coordinate on a circle
whose circumference is the actual cone angle. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- Each sector contributes its cumulative starting angle and its ordinary offset. -/
noncomputable def fanCirclePiece (pole : Fin 6) (i : Fin 4) (x : Space) :
    AddCircle (graph.totalAngleAt pole) :=
  (graph.openingAngle pole 0 i.castSucc + graph.fanOffset pole i x : ℝ)

/-- The domain excludes just the cone point, where direction is undefined. -/
def fanCircleDomain (pole : Fin 6) : Set Space :=
  (⋃ i : Fin 4, graph.triangle (fanTriangle pole i)) \ {(graph.vertex pole : Space)}

/-- Choose any incident sector containing the point. Agreement is proved below. -/
noncomputable def fanCircleMap (pole : Fin 6) (x : Space) : AddCircle (graph.totalAngleAt pole) := by
  classical
  exact if h : ∃ i : Fin 4, x ∈ graph.triangle (fanTriangle pole i)
    then graph.fanCirclePiece pole h.choose x else 0

variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- Cumulative angles agree modulo the cone angle at every radial seam. -/
theorem fanCirclePiece_adjacent (pole : Fin 6) (i : Fin 4) (x : Space)
    (first : x ∈ graph.triangle (fanTriangle pole i))
    (second : x ∈ graph.triangle (fanTriangle pole (i + 1)))
    (nonpole : x ≠ graph.vertex pole) :
    graph.fanCirclePiece pole i x = graph.fanCirclePiece pole (i + 1) x := by
  obtain ⟨full, zero⟩ := graph.adjacent_sector_offsets small_faces pole i x first second nonpole
  simp only [fanCirclePiece, full, zero, add_zero]
  have last := graph.openingAngle_last pole 0
  fin_cases i
  · simp [openingAngle]
  · rfl
  · rfl
  · change ((graph.openingAngle pole 0 4 : ℝ) : AddCircle (graph.totalAngleAt pole)) = (0 : ℝ)
    rw [last, AddCircle.coe_period, AddCircle.coe_zero]

include small_faces in
/-- Every possible choice of containing sector gives the same circle point. -/
theorem fanCirclePiece_joined (pole : Fin 6) (i j : Fin 4) (x : Space)
    (first : x ∈ graph.triangle (fanTriangle pole i))
    (second : x ∈ graph.triangle (fanTriangle pole j)) (nonpole : x ≠ graph.vertex pole) :
    graph.fanCirclePiece pole i x = graph.fanCirclePiece pole j x := by
  by_cases same : i = j
  · rw [same]
  rcases graph.common_sector_ray small_faces pole i j same x first second nonpole with h | h
  · obtain ⟨h, _⟩ := h
    subst j
    exact graph.fanCirclePiece_adjacent small_faces pole i x first second nonpole
  · obtain ⟨h, _⟩ := h
    subst i
    exact (graph.fanCirclePiece_adjacent small_faces pole j x second first nonpole).symm

include small_faces in
theorem fanCircleMap_on_sector (pole : Fin 6) (i : Fin 4) (x : Space)
    (member : x ∈ graph.triangle (fanTriangle pole i)) (nonpole : x ≠ graph.vertex pole) :
    graph.fanCircleMap pole x = graph.fanCirclePiece pole i x := by
  classical
  rw [fanCircleMap, dif_pos ⟨i, member⟩]
  exact graph.fanCirclePiece_joined small_faces pole _ i x
    (Exists.choose_spec (⟨i, member⟩ : ∃ j : Fin 4, x ∈ graph.triangle (fanTriangle pole j)))
    member nonpole

/-- Each sector formula is continuous away from the pole. -/
theorem fanCirclePiece_continuousAt (pole : Fin 6) (i : Fin 4) (x : Space)
    (nonpole : x ≠ graph.vertex pole) : ContinuousAt (graph.fanCirclePiece pole i) x := by
  have angle_continuous : ContinuousAt (fun y : Space => graph.fanOffset pole i y) x :=
    (EuclideanGeometry.continuousAt_angle
      (x := ((graph.vertex (fanNeighbor pole i) : Space), (graph.vertex pole : Space), x))
      (graph.fan_neighbor_distinct pole i) nonpole).comp
      (f := fun y : Space => ((graph.vertex (fanNeighbor pole i) : Space),
        (graph.vertex pole : Space), y))
      (show ContinuousAt (fun y : Space => ((graph.vertex (fanNeighbor pole i) : Space),
        (graph.vertex pole : Space), y)) x by fun_prop)
  exact (AddCircle.continuous_mk' (graph.totalAngleAt pole)).continuousAt.comp
    (continuousAt_const.add angle_continuous)

include small_faces in
/-- The sector formulas paste to one continuous angular coordinate on the actual fan. -/
theorem fanCircleMap_continuousOn (pole : Fin 6) :
    ContinuousOn (graph.fanCircleMap pole) (graph.fanCircleDomain pole) := by
  rw [continuousOn_iff_continuous_restrict]
  let pieces (i : Fin 4) : Set (graph.fanCircleDomain pole) :=
    {x | (x : Space) ∈ graph.triangle (fanTriangle pole i)}
  have closed (i : Fin 4) : IsClosed (pieces i) :=
    (graph.triangle_isCompact _).isClosed.preimage continuous_subtype_val
  have covers : (univ : Set (graph.fanCircleDomain pole)) = ⋃ i, pieces i := by
    ext x
    constructor
    · intro _
      obtain ⟨i, hi⟩ := mem_iUnion.mp x.property.1
      exact mem_iUnion.mpr ⟨i, hi⟩
    · intro _
      trivial
  rw [← continuousOn_univ, covers]
  apply (locallyFinite_of_finite pieces).continuousOn_iUnion closed
  intro i
  have formula : Continuous (fun x : graph.fanCircleDomain pole => graph.fanCirclePiece pole i x) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (graph.fanCirclePiece_continuousAt pole i x x.property.2).comp continuous_subtype_val.continuousAt
  exact formula.continuousOn.congr (fun x hx => graph.fanCircleMap_on_sector small_faces pole i x hx x.property.2)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
