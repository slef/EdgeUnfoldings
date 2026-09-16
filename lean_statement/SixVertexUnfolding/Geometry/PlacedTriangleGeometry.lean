import SixVertexUnfolding.Geometry.PlacedTriangleSides
import SixVertexUnfolding.Geometry.OutwardTriangle
import SixVertexUnfolding.Geometry.TriangleTopology

/-! Each globally placed kite consists of two nondegenerate triangles
with disjoint interiors and no overlap away from their common base. -/

namespace SixVertexUnfolding.ConvexPolyhedron.PlacedCutEdgeTriangles

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (D : PlacedCutEdgeTriangles T edge)

def sideRegion (side : Bool) : Set Plane :=
  convexHull ℝ ({D.motion (D.apex side), D.motion D.model.left, D.motion D.model.right} : Set Plane)

theorem side_noncollinear (side : Bool) :
    ¬ Collinear ℝ ({D.motion (D.apex side), D.motion D.model.left, D.motion D.model.right} : Set Plane) := by
  apply plane_motion_noncollinear
  cases side
  · exact D.model.noncollinear.1
  · exact D.model.noncollinear.2

theorem side_regular (side : Bool) : closure (interior (D.sideRegion side)) = D.sideRegion side :=
  planar_triangle_regular _ _ _ (D.side_noncollinear side)

theorem side_subset_kite (side : Bool) : D.sideRegion side ⊆ D.kite := by
  cases side
  · exact subset_union_left
  · exact subset_union_right

/-- Even the closed triangle on one side misses the other triangle's interior. -/
theorem sides_nonoverlap (side other : Bool) (different : side ≠ other) :
    Disjoint (D.sideRegion side) (interior (D.sideRegion other)) := by
  have opposite := bisector_sites_opposite (D.motion D.model.first) (D.motion D.model.second)
    (D.motion D.model.left) (D.motion D.model.right) (D.motion.injective.ne D.model.distinct_sources)
    (D.motion.injective.ne D.model.base_different)
    (by simpa only [D.motion.dist_map] using D.model.left_distances)
    (by simpa only [D.motion.dist_map] using D.model.right_distances)
  have noncollinear : ¬ Collinear ℝ
      ({D.motion D.model.left, D.motion D.model.right, D.motion D.model.first} : Set Plane) :=
    plane_motion_noncollinear D.motion _ _ _ D.model.base_first_noncollinear
  have separated := opposite_triangles_disjoint (D.motion D.model.left) (D.motion D.model.right)
    (D.motion D.model.first) (D.motion D.model.second) noncollinear
    ((oppositeHingeSides_iff_det _ _ _ _ (D.motion.injective.ne D.model.base_different)).mpr opposite.le)
  have basic : Disjoint (interior (D.sideRegion false)) (interior (D.sideRegion true)) := by
    have rotate (p l r : Plane) : ({l, r, p} : Set Plane) = {p, l, r} := by
      ext q
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    rw [rotate (D.motion D.model.first) (D.motion D.model.left) (D.motion D.model.right),
      rotate (D.motion D.model.second) (D.motion D.model.left) (D.motion D.model.right)] at separated
    exact separated
  have both : Disjoint (interior (D.sideRegion side)) (interior (D.sideRegion other)) := by
    cases side <;> cases other
    · exact (different rfl).elim
    · exact basic
    · exact basic.symm
    · exact (different rfl).elim
  have closed := both.closure_left isOpen_interior
  rwa [D.side_regular side] at closed

/-- A point in a triangle interior has only its actual surface preimage in that kite. -/
theorem interior_placement_unique (side : Bool) {b c : frontier P.body}
    (inside : b ∈ range (closedRouteStripMap (D.routes side)))
    (interior_point : ((D.sideTriangle side).homeomorph ⟨b, inside⟩ : Plane) ∈ interior (D.sideRegion side))
    (other : D.Places c ((D.sideTriangle side).homeomorph ⟨b, inside⟩)) : b = c := by
  obtain ⟨other_side, other_inside, same⟩ := other
  by_cases sides : side = other_side
  · subst other_side
    have preimages := (D.sideTriangle side).homeomorph.injective (Subtype.ext same.symm)
    exact congrArg Subtype.val preimages
  · have in_other : ((D.sideTriangle side).homeomorph ⟨b, inside⟩ : Plane) ∈ D.sideRegion other_side :=
      same ▸ ((D.sideTriangle other_side).homeomorph ⟨c, other_inside⟩).property
    exact (disjoint_left.mp (D.sides_nonoverlap other_side side (Ne.symm sides)) in_other interior_point).elim

end SixVertexUnfolding.ConvexPolyhedron.PlacedCutEdgeTriangles
