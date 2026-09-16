import SixVertexUnfolding.Geometry.SixVertexFacets
import SixVertexUnfolding.Geometry.NamedQuadrilateral
import SixVertexUnfolding.OctahedralTriangles

/-! The common eight triangles are genuine subsets of whole original facets. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- The spatial convex hull of a finite set of original vertex labels. -/
def labeledHull (labels : Finset (Fin 6)) : Set Space :=
  convexHull ℝ ((fun i => (graph.vertex i : Space)) '' (labels : Set (Fin 6)))

/-- A subdivision triangle, still in the original solid. -/
def triangle (t : Fin 8) : Set Space := graph.labeledHull (OctahedralTriangles.vertices t)

/-- Its three spatial corners. -/
def trianglePoint (t : Fin 8) (i : Fin 3) : Space := graph.vertex (corner t i)

/-- A whole original facet is the hull of its labeled original vertices. -/
theorem face_eq_labeledHull (F : P.Face) : F.val = graph.labeledHull (F.vertexLabels graph.vertex) := by
  rw [labeledHull, F.image_vertexLabels]
  exact F.eq_convexHull_vertices

theorem labeledHull_mono {left right : Finset (Fin 6)} (subset : left ⊆ right) :
    graph.labeledHull left ⊆ graph.labeledHull right :=
  convexHull_mono (Set.image_mono (Finset.coe_subset.mpr subset))

/-- A triple of labels gives the usual closed spatial triangle. -/
theorem labeledHull_triple (a b c : Fin 6) : graph.labeledHull {a, b, c} =
    convexHull ℝ ({(graph.vertex a : Space), (graph.vertex b : Space), (graph.vertex c : Space)} : Set Space) := by
  simp [labeledHull, Set.image_insert_eq, Set.image_singleton]

/-- The hull notation agrees with the three named spatial triangle corners. -/
theorem triangle_eq_hull_corners (t : Fin 8) : graph.triangle t =
    convexHull ℝ ({graph.trianglePoint t 0, graph.trianglePoint t 1, graph.trianglePoint t 2} : Set Space) := by
  have labels : (OctahedralTriangles.vertices t : Set (Fin 6)) = Set.range (corner t) := by simp [OctahedralTriangles.vertices]
  rw [triangle, labeledHull, labels, ← Set.range_comp]
  congr 1
  ext x
  simp only [Function.comp_def, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [trianglePoint]
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-- Every triangle has three different genuine vertices. -/
theorem trianglePoint_injective (t : Fin 8) : Function.Injective (graph.trianglePoint t) := by
  intro i j same
  exact corner_injective t (graph.vertex.injective (Subtype.ext same))

/-- None of the eight subdivision triangles is degenerate. -/
theorem triangle_not_collinear (t : Fin 8) :
    ¬ Collinear ℝ ({graph.trianglePoint t 0, graph.trianglePoint t 1, graph.trianglePoint t 2} : Set Space) :=
  P.no_three_collinear_vertices (graph.vertex (corner t 0)).property
    (graph.vertex (corner t 1)).property (graph.vertex (corner t 2)).property
    ((graph.trianglePoint_injective t).ne (by decide))
    ((graph.trianglePoint_injective t).ne (by decide))
    ((graph.trianglePoint_injective t).ne (by decide))

variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

/-- The actual whole original facet carrying this subdivision triangle. -/
noncomputable def triangleFace (t : Fin 8) : P.Face :=
  ((graph.exists_facet_iff small_faces (carrier graph.kind t)).mpr (carrier_mem_facets _ _)).choose

@[simp] theorem triangleFace_labels (t : Fin 8) :
    (graph.triangleFace small_faces t).vertexLabels graph.vertex = carrier graph.kind t :=
  ((graph.exists_facet_iff small_faces (carrier graph.kind t)).mpr (carrier_mem_facets _ _)).choose_spec

/-- Each closed triangle lies in its assigned original whole facet. -/
theorem triangle_subset_face (t : Fin 8) :
    graph.triangle t ⊆ (graph.triangleFace small_faces t).val := by
  rw [graph.face_eq_labeledHull, graph.triangleFace_labels]
  exact graph.labeledHull_mono (vertices_subset_carrier _ _)

/-- Every corner belongs to its assigned original whole facet. -/
theorem trianglePoint_mem_face (t : Fin 8) (i : Fin 3) :
    graph.trianglePoint t i ∈ (graph.triangleFace small_faces t).val := by
  apply graph.triangle_subset_face small_faces t
  apply subset_convexHull ℝ _
  exact ⟨corner t i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, rfl⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
