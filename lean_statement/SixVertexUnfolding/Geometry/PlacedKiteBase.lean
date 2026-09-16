import SixVertexUnfolding.Geometry.PlacedTriangleGeometry

/-! The two inverse triangle maps coincide on their whole common
base. Their different planar source corners remain distinct. -/

namespace SixVertexUnfolding.ConvexPolyhedron.PlacedCutEdgeTriangles

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (D : PlacedCutEdgeTriangles T edge)

theorem side_intersection : D.sideRegion false ∩ D.sideRegion true =
    segment ℝ (D.motion D.model.left) (D.motion D.model.right) := by
  have intersection := bisector_kite_intersection (D.motion D.model.first) (D.motion D.model.second)
    (D.motion D.model.left) (D.motion D.model.right) (D.motion.injective.ne D.model.distinct_sources)
    (D.motion.injective.ne D.model.base_different)
    (by simpa only [D.motion.dist_map] using D.model.left_distances)
    (by simpa only [D.motion.dist_map] using D.model.right_distances)
  have rotate (p l r : Plane) : ({l, r, p} : Set Plane) = {p, l, r} := by
    ext q
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  rw [rotate (D.motion D.model.first) (D.motion D.model.left) (D.motion D.model.right),
    rotate (D.motion D.model.second) (D.motion D.model.left) (D.motion D.model.right)] at intersection
  exact intersection

/-- The entire triangle base folds to the actual parametrized cut-tree edge. -/
theorem fold_on_base (side : Bool) (s : unitInterval)
    (inside : AffineMap.lineMap (D.motion D.model.left) (D.motion D.model.right) (s : ℝ) ∈ D.sideRegion side) :
    (((D.sideTriangle side).homeomorph.symm ⟨_, inside⟩).val : frontier P.body) = T.closedEdgeTarget edge s := by
  let b := closedRouteStripMap (D.routes side) (s, 1)
  have mapped : ((D.sideTriangle side).homeomorph ⟨b, mem_range_self _⟩ : Plane) =
      AffineMap.lineMap (D.motion D.model.left) (D.motion D.model.right) (s : ℝ) := by
    rw [(D.sideTriangle side).radial]
    exact AffineMap.lineMap_apply_one _ _
  have point : (D.sideTriangle side).homeomorph ⟨b, mem_range_self _⟩ = ⟨_, inside⟩ := Subtype.ext mapped
  rw [← point, (D.sideTriangle side).homeomorph.symm_apply_apply]
  exact congrArg Prod.snd (D.routes_member side s).2

/-- All planar contacts between the two sides have the same actual surface preimage. -/
theorem side_folds_agree (side other : Bool) (x : Plane) (first : x ∈ D.sideRegion side)
    (second : x ∈ D.sideRegion other) :
    ((D.sideTriangle side).homeomorph.symm ⟨x, first⟩).val =
      ((D.sideTriangle other).homeomorph.symm ⟨x, second⟩).val := by
  by_cases same : side = other
  · subst other
    rfl
  have base : x ∈ segment ℝ (D.motion D.model.left) (D.motion D.model.right) := by
    rw [← D.side_intersection]
    cases side <;> cases other
    · exact (same rfl).elim
    · exact ⟨first, second⟩
    · exact ⟨second, first⟩
    · exact (same rfl).elim
  rw [segment_eq_image_lineMap] at base
  obtain ⟨s, unit, rfl⟩ := base
  exact (D.fold_on_base side ⟨s, unit⟩ first).trans (D.fold_on_base other ⟨s, unit⟩ second).symm

end SixVertexUnfolding.ConvexPolyhedron.PlacedCutEdgeTriangles
