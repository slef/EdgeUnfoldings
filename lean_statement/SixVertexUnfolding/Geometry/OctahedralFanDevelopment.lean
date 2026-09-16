import SixVertexUnfolding.Geometry.OctahedralFanSeparation
import SixVertexUnfolding.Geometry.PrescribedTrianglePlacement

/-! Simultaneous rigid placements realize the explicit opened fan on the actual solid. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

/-- Each actual fan facet can be placed at its prescribed three opened corners. -/
theorem exists_opening_facet_placement (pole : Fin 6) (slit i : Fin 4) :
    ∃ place : Space →ᵃ[ℝ] Plane,
      place (graph.vertex pole) = 0 ∧
      place (graph.vertex (fanNeighbor pole (slit + i))) = graph.openingPoint pole slit i.castSucc ∧
      place (graph.vertex (fanNeighbor pole ((slit + i) + 1))) = graph.openingPoint pole slit i.succ ∧
      ∀ x ∈ (graph.triangleFace small_faces (fanTriangle pole (slit + i))).val,
        ∀ y ∈ (graph.triangleFace small_faces (fanTriangle pole (slit + i))).val,
          dist (place x) (place y) = dist x y := by
  apply (graph.triangleFace small_faces (fanTriangle pole (slit + i))).exists_placement_at_triangle
    (graph.vertex pole) (graph.vertex (fanNeighbor pole (slit + i)))
    (graph.vertex (fanNeighbor pole ((slit + i) + 1)))
  · exact graph.vertex.injective.ne (fanNeighbor_ne_source pole (slit + i)).symm
  · exact graph.vertex.injective.ne (fanNeighbor_ne_source pole ((slit + i) + 1)).symm
  · exact graph.vertex.injective.ne ((fanNeighbor_injective pole).ne ((by decide : ∀ i : Fin 4, i ≠ i + 1) (slit + i)))
  · exact graph.fan_sector_on_face pole small_faces (slit + i) _ (by simp)
  · exact graph.fan_sector_on_face pole small_faces (slit + i) _ (by simp)
  · exact graph.fan_sector_on_face pole small_faces (slit + i) _ (by simp)
  · rw [graph.openingPoint_radius, openingVertex_start]
  · rw [graph.openingPoint_radius, openingVertex_end]
  · exact graph.openingPoint_base pole slit i

/-- Four coherent facet placements, with one common pole and five successive equator copies. -/
structure FanDevelopment (pole : Fin 6) (slit : Fin 4) where
  place : Fin 4 → Space →ᵃ[ℝ] Plane
  at_pole : ∀ i, place i (graph.vertex pole) = 0
  at_left : ∀ i, place i (graph.vertex (fanNeighbor pole (slit + i))) = graph.openingPoint pole slit i.castSucc
  at_right : ∀ i, place i (graph.vertex (fanNeighbor pole ((slit + i) + 1))) = graph.openingPoint pole slit i.succ
  rigid : ∀ i, ∀ x ∈ (graph.triangleFace small_faces (fanTriangle pole (slit + i))).val,
    ∀ y ∈ (graph.triangleFace small_faces (fanTriangle pole (slit + i))).val,
      dist (place i x) (place i y) = dist x y

theorem exists_fan_development (pole : Fin 6) (slit : Fin 4) :
    Nonempty (graph.FanDevelopment small_faces pole slit) := by
  classical
  choose place at_pole at_left at_right rigid using graph.exists_opening_facet_placement small_faces pole slit
  exact ⟨⟨place, at_pole, at_left, at_right, rigid⟩⟩

namespace FanDevelopment

variable {graph small_faces} {pole : Fin 6} {slit : Fin 4}
variable (fan : graph.FanDevelopment small_faces pole slit)

/-- Each placed subdivision triangle is exactly the corresponding polar-coordinate triangle. -/
theorem placed_triangle (i : Fin 4) :
    fan.place i '' graph.triangle (fanTriangle pole (slit + i)) = graph.openingTriangle pole slit i := by
  rw [triangle, fanTriangle_vertices, graph.labeledHull_triple, (fan.place i).image_convexHull,
    Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, fan.at_pole, fan.at_left, fan.at_right]
  rfl

/-- Every pair of these actual placed fan triangles has disjoint interiors. -/
theorem nonoverlap (i j : Fin 4) (different : i ≠ j) :
    Disjoint (interior (fan.place i '' graph.triangle (fanTriangle pole (slit + i))))
      (interior (fan.place j '' graph.triangle (fanTriangle pole (slit + j)))) := by
  rw [fan.placed_triangle, fan.placed_triangle]
  exact graph.openingTriangles_disjoint small_faces pole slit i j different

/-- Consecutive fan triangles agree on their entire common radial hinge. -/
theorem joined (i : Fin 3) :
    ∀ x ∈ segment ℝ (graph.vertex pole : Space) (graph.vertex (fanNeighbor pole ((slit + i.castSucc) + 1))),
      fan.place i.castSucc x = fan.place i.succ x := by
  have indices : (i.castSucc : Fin 4) + 1 = i.succ := by fin_cases i <;> decide
  have rays : ((i.castSucc : Fin 4).succ : Fin 5) = (i.succ : Fin 4).castSucc := by fin_cases i <;> rfl
  have endpoint : fan.place i.castSucc (graph.vertex (fanNeighbor pole ((slit + i.castSucc) + 1))) =
      fan.place i.succ (graph.vertex (fanNeighbor pole ((slit + i.castSucc) + 1))) := by
    rw [fan.at_right, add_assoc, indices, fan.at_left, rays]
  have agree : Set.EqOn (fan.place i.castSucc) (fan.place i.succ)
      ({(graph.vertex pole : Space), (graph.vertex (fanNeighbor pole ((slit + i.castSucc) + 1)) : Space)} : Set Space) := by
    rintro x (rfl | rfl)
    · rw [fan.at_pole, fan.at_pole]
    · exact endpoint
  intro x member
  apply AffineMap.eqOn_affineSpan agree
  rw [← convexHull_pair] at member
  exact convexHull_subset_affineSpan _ member

end FanDevelopment
end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
