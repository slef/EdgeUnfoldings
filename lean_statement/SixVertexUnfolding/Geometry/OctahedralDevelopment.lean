import SixVertexUnfolding.Geometry.OctahedralFanDevelopment
import SixVertexUnfolding.Geometry.OctahedralPetalPlacement

/-! One coherent four-triangle fan with its four outward petals, at any source and slit. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

/-- The eight developed triangles share the chosen fan opening and four outward equator hinges.
Whole-facet consistency across auxiliary hinges is a later reassembly obligation. -/
structure Development (source : Fin 6) (slit : Fin 4) where
  fan : graph.FanDevelopment small_faces (opposite source) slit
  patch : ∀ i : Fin 4, graph.DevelopedPatch source (slit + i)
  patch_pole : ∀ i, (patch i).pole = 0
  patch_left : ∀ i, (patch i).left = graph.openingPoint (opposite source) slit i.castSucc
  patch_right : ∀ i, (patch i).right = graph.openingPoint (opposite source) slit i.succ
  petal : Fin 4 → Space →ᵃ[ℝ] Plane
  petal_left : ∀ i, petal i (graph.vertex (fanNeighbor source (slit + i))) = (patch i).left
  petal_right : ∀ i, petal i (graph.vertex (fanNeighbor source ((slit + i) + 1))) = (patch i).right
  petal_apex : ∀ i, petal i (graph.vertex source) = (patch i).apex
  petal_rigid : ∀ i, ∀ x ∈ (graph.triangleFace small_faces (fanTriangle source (slit + i))).val,
    ∀ y ∈ (graph.triangleFace small_faces (fanTriangle source (slit + i))).val,
      dist (petal i x) (petal i y) = dist x y

/-- Every source and every slit admit this simultaneous outward development. -/
theorem exists_development (source : Fin 6) (slit : Fin 4) : Nonempty (graph.Development small_faces source slit) := by
  classical
  obtain ⟨fan⟩ := graph.exists_fan_development small_faces (opposite source) slit
  have patches : ∀ i : Fin 4, ∃ patch : graph.DevelopedPatch source (slit + i),
      patch.pole = 0 ∧ patch.left = graph.openingPoint (opposite source) slit i.castSucc ∧
      patch.right = graph.openingPoint (opposite source) slit i.succ := by
    intro i
    obtain ⟨patch, pole, left, right⟩ := graph.exists_patch_of_fan_placement small_faces source (slit + i)
      (fan.place i) (fan.rigid i)
    have paired : ∀ s j, fanNeighbor (opposite s) j = fanNeighbor s j := by decide
    refine ⟨patch, ?_, ?_, ?_⟩
    · rw [pole, fan.at_pole]
    · rw [left, ← paired source (slit + i), fan.at_left]
    · rw [right, ← paired source ((slit + i) + 1), fan.at_right]
  choose patch patch_pole patch_left patch_right using patches
  choose petal petal_left petal_right petal_apex petal_rigid using
    fun i => (patch i).exists_petal_placement small_faces
  exact ⟨⟨fan, patch, patch_pole, patch_left, patch_right, petal, petal_left, petal_right, petal_apex, petal_rigid⟩⟩

namespace Development

variable {graph small_faces} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The actual fan triangle has the three corners recorded by its patch. -/
theorem fan_triangle (i : Fin 4) :
    net.fan.place i '' graph.triangle (fanTriangle (opposite source) (slit + i)) =
      convexHull ℝ ({(net.patch i).pole, (net.patch i).left, (net.patch i).right} : Set Plane) := by
  rw [net.fan.placed_triangle, net.patch_pole, net.patch_left, net.patch_right]
  rfl

/-- The actual petal has exactly its copied apex and the two common hinge endpoints. -/
theorem petal_triangle (i : Fin 4) :
    net.petal i '' graph.triangle (fanTriangle source (slit + i)) =
      convexHull ℝ ({(net.patch i).apex, (net.patch i).left, (net.patch i).right} : Set Plane) := by
  rw [triangle, fanTriangle_vertices, graph.labeledHull_triple, (net.petal i).image_convexHull,
    Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    net.petal_apex, net.petal_left, net.petal_right]

/-- Every petal is disjoint in interior from the fan triangle carrying it. -/
theorem attached_pair_nonoverlap (i : Fin 4) :
    Disjoint (interior (net.fan.place i '' graph.triangle (fanTriangle (opposite source) (slit + i))))
      (interior (net.petal i '' graph.triangle (fanTriangle source (slit + i)))) := by
  rw [net.fan_triangle, net.petal_triangle]
  have reorder (x a b : Plane) : ({x, a, b} : Set Plane) = {a, b, x} := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [reorder (net.patch i).pole, reorder (net.patch i).apex]
  exact opposite_triangles_disjoint _ _ _ _ (net.patch i).fan_noncollinear (net.patch i).outward

/-- The petal and its fan triangle agree on the entire equator hinge. -/
theorem petal_joined (i : Fin 4) :
    ∀ x ∈ segment ℝ (graph.vertex (fanNeighbor source (slit + i)) : Space)
      (graph.vertex (fanNeighbor source ((slit + i) + 1))), net.fan.place i x = net.petal i x := by
  have paired : ∀ s j, fanNeighbor (opposite s) j = fanNeighbor s j := by decide
  have agree : Set.EqOn (net.fan.place i) (net.petal i)
      ({(graph.vertex (fanNeighbor source (slit + i)) : Space),
        (graph.vertex (fanNeighbor source ((slit + i) + 1)) : Space)} : Set Space) := by
    rintro x (rfl | rfl)
    · rw [net.petal_left, net.patch_left, ← paired source (slit + i), net.fan.at_left]
    · rw [net.petal_right, net.patch_right, ← paired source ((slit + i) + 1), net.fan.at_right]
  intro x member
  apply AffineMap.eqOn_affineSpan agree
  rw [← convexHull_pair] at member
  exact convexHull_subset_affineSpan _ member

end Development
end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
