import SixVertexUnfolding.Geometry.OctahedralCoverage
import SixVertexUnfolding.Geometry.NonoverlapReassembly
import SixVertexUnfolding.Geometry.TriangleTopology
import SixVertexUnfolding.Geometry.TriangleNondegeneracy

/-! A nonoverlapping subdivision certifies the original whole-face unfolding. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)

/-- A placed subdivision triangle is exactly the triangle on its three placed corners. -/
theorem placed_subdivision_triangle (t : Fin 8) (place : Space →ᵃ[ℝ] Plane) :
    place '' graph.triangle t = convexHull ℝ
      ({place (graph.trianglePoint t 0), place (graph.trianglePoint t 1), place (graph.trianglePoint t 2)} : Set Plane) := by
  rw [graph.triangle_eq_hull_corners, place.image_convexHull,
    Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]

/-- Rigidity of the containing whole facet makes the triangle's planar interior dense in it. -/
theorem placed_subdivision_regular (t : Fin 8) (place : Space →ᵃ[ℝ] Plane)
    (rigid : ∀ x ∈ (graph.triangleFace small_faces t).val, ∀ y ∈ (graph.triangleFace small_faces t).val,
      dist (place x) (place y) = dist x y) :
    closure (interior (place '' graph.triangle t)) = place '' graph.triangle t := by
  have distance (i j : Fin 3) : dist (place (graph.trianglePoint t i)) (place (graph.trianglePoint t j)) =
      dist (graph.trianglePoint t i) (graph.trianglePoint t j) :=
    rigid _ (graph.trianglePoint_mem_face small_faces t i) _ (graph.trianglePoint_mem_face small_faces t j)
  have distinct (i j : Fin 3) (different : i ≠ j) : graph.vertex (corner t i) ≠ graph.vertex (corner t j) :=
    graph.vertex.injective.ne ((corner_injective t).ne different)
  have noncollinear := P.placed_triangle_noncollinear
    (graph.vertex (corner t 0)) (graph.vertex (corner t 1)) (graph.vertex (corner t 2))
    (distinct 0 1 (by decide)) (distinct 0 2 (by decide)) (distinct 1 2 (by decide))
    (place (graph.trianglePoint t 0)) (place (graph.trianglePoint t 1)) (place (graph.trianglePoint t 2))
    (distance 0 1) (distance 0 2) (distance 1 2)
  rw [graph.placed_subdivision_triangle]
  exact planar_triangle_regular _ _ _ noncollinear

/-- Checking triangle pairs from different original facets suffices for whole-facet nonoverlap. -/
theorem original_faces_nonoverlap (place : P.Face → Space →ᵃ[ℝ] Plane)
    (rigid : ∀ F, ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place F x) (place F y) = dist x y)
    (safe : ∀ t u : Fin 8, graph.triangleFace small_faces t ≠ graph.triangleFace small_faces u →
      Disjoint (interior (place (graph.triangleFace small_faces t) '' graph.triangle t))
        (interior (place (graph.triangleFace small_faces u) '' graph.triangle u))) :
    ∀ F G : P.Face, F ≠ G → Disjoint (interior (place F '' F.val)) (interior (place G '' G.val)) := by
  intro F G different
  let left_piece (t : {t : Fin 8 // graph.triangleFace small_faces t = F}) := place F '' graph.triangle t
  let right_piece (t : {t : Fin 8 // graph.triangleFace small_faces t = G}) := place G '' graph.triangle t
  have cover (F : P.Face) : place F '' F.val ⊆
      ⋃ (t : {t : Fin 8 // graph.triangleFace small_faces t = F}), place F '' graph.triangle t := by
    rintro z ⟨x, on_face, rfl⟩
    rw [graph.face_eq_subdivision_triangles small_faces F] at on_face
    obtain ⟨t, on_face⟩ := Set.mem_iUnion.mp on_face
    obtain ⟨same, on_triangle⟩ := Set.mem_iUnion.mp on_face
    exact Set.mem_iUnion.mpr ⟨⟨t, same⟩, ⟨x, on_triangle, rfl⟩⟩
  apply disjoint_interiors_of_piece_covers _ _ left_piece right_piece (cover F) (cover G)
  · intro t
    apply graph.placed_subdivision_regular small_faces t (place F)
    rw [t.property]
    exact rigid F
  · intro t
    apply graph.placed_subdivision_regular small_faces t (place G)
    rw [t.property]
    exact rigid G
  · intro t u
    have distinct : graph.triangleFace small_faces t ≠ graph.triangleFace small_faces u := by
      rw [t.property, u.property]
      exact different
    simpa only [t.property, u.property] using safe t u distinct

/-- The subdivision certificate gives the unchanged public original-edge unfolding. -/
theorem hasEdgeUnfolding_of_subdivision (place : P.Face → Space →ᵃ[ℝ] Plane)
    (hinges : SimpleGraph P.Face) (tree : hinges.IsTree)
    (original : ∀ F G, hinges.Adj F G → P.ShareEdge F G)
    (rigid : ∀ F, ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place F x) (place F y) = dist x y)
    (joined : ∀ F G, hinges.Adj F G → ∀ x ∈ F.val ∩ G.val, place F x = place G x)
    (safe : ∀ t u : Fin 8, graph.triangleFace small_faces t ≠ graph.triangleFace small_faces u →
      Disjoint (interior (place (graph.triangleFace small_faces t) '' graph.triangle t))
        (interior (place (graph.triangleFace small_faces u) '' graph.triangle u))) : P.HasEdgeUnfolding :=
  ⟨{
    place := fun F => place F
    hinges := hinges
    tree := tree
    original_edges := original
    rigid := rigid
    joined := joined
    nonoverlap := graph.original_faces_nonoverlap small_faces place rigid safe
  }⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
