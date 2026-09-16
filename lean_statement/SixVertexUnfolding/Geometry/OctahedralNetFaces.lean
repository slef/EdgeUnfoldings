import SixVertexUnfolding.Geometry.OctahedralDevelopment
import SixVertexUnfolding.OctahedralNet

/-! For an octahedron, the eight developed triangles are exactly the eight original facets. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

/-- The actual whole facet assigned to one position in the eight-triangle net. -/
noncomputable def netFace (source : Fin 6) (slit : Fin 4) (index : OctahedralNet.FaceIndex) : P.Face :=
  graph.triangleFace small_faces (OctahedralNet.triangle source slit index)

variable (octahedral : graph.kind = .octahedron)

include octahedral in
theorem netFace_labels (source : Fin 6) (slit : Fin 4) (index : OctahedralNet.FaceIndex) :
    (graph.netFace small_faces source slit index).vertexLabels graph.vertex =
      OctahedralTriangles.vertices (OctahedralNet.triangle source slit index) := by
  rw [netFace, graph.triangleFace_labels, octahedral, OctahedralNet.octahedron_carrier]

include octahedral in
/-- In the octahedron case, each subdivision triangle is already a whole original facet. -/
theorem netFace_eq_triangle (source : Fin 6) (slit : Fin 4) (index : OctahedralNet.FaceIndex) :
    (graph.netFace small_faces source slit index).val = graph.triangle (OctahedralNet.triangle source slit index) := by
  rw [graph.face_eq_labeledHull, graph.netFace_labels small_faces octahedral]
  rfl

include octahedral in
theorem netFace_injective (source : Fin 6) (slit : Fin 4) :
    Function.Injective (graph.netFace small_faces source slit) := by
  intro x y same
  have labels := congrArg (fun F : P.Face => F.vertexLabels graph.vertex) same
  change (graph.netFace small_faces source slit x).vertexLabels graph.vertex =
    (graph.netFace small_faces source slit y).vertexLabels graph.vertex at labels
  rw [graph.netFace_labels small_faces octahedral, graph.netFace_labels small_faces octahedral] at labels
  exact (OctahedralNet.triangle_bijective source slit).1 (OctahedralNet.vertices_injective labels)

include octahedral in
theorem netFace_surjective (source : Fin 6) (slit : Fin 4) :
    Function.Surjective (graph.netFace small_faces source slit) := by
  intro F
  have member : F.vertexLabels graph.vertex ∈ SmallGraphs.SixGraphKind.octahedron.facets := by
    rw [← octahedral, ← graph.labeledFacets_eq small_faces, mem_labeledFacets]
    exact ⟨F, rfl⟩
  obtain ⟨t, labels⟩ := (by decide : ∀ face : Finset (Fin 6), face ∈ SmallGraphs.SixGraphKind.octahedron.facets →
    ∃ t, OctahedralTriangles.vertices t = face) _ member
  obtain ⟨index, at_triangle⟩ := (OctahedralNet.triangle_bijective source slit).2 t
  refine ⟨index, Face.vertexLabels_injective graph.vertex ?_⟩
  change (graph.netFace small_faces source slit index).vertexLabels graph.vertex = F.vertexLabels graph.vertex
  rw [graph.netFace_labels small_faces octahedral, at_triangle]
  exact labels

/-- Concrete net positions identify all and only the actual original octahedron facets. -/
noncomputable def netFaceEquiv (source : Fin 6) (slit : Fin 4) : OctahedralNet.FaceIndex ≃ P.Face :=
  Equiv.ofBijective (graph.netFace small_faces source slit)
    ⟨graph.netFace_injective small_faces octahedral source slit, graph.netFace_surjective small_faces octahedral source slit⟩

/-- Intersection of original facets is the hull of their common labeled original vertices. -/
theorem intersection_eq_labeledHull (F G : P.Face) :
    F.val ∩ G.val = graph.labeledHull (F.vertexLabels graph.vertex ∩ G.vertexLabels graph.vertex) := by
  have injective : Function.Injective (fun i => (graph.vertex i : Space)) :=
    fun _ _ same => graph.vertex.injective (Subtype.ext same)
  rw [F.intersection_eq_convexHull_vertices G, labeledHull, Finset.coe_inter,
    Set.image_inter injective, F.image_vertexLabels, G.image_vertexLabels]
  congr 1
  ext x
  simp only [Set.mem_inter_iff]
  tauto

include octahedral in
/-- Every one of the seven chosen net hinges is an original polyhedron edge. -/
theorem net_hinge_original (source : Fin 6) (slit : Fin 4) (x y : OctahedralNet.FaceIndex)
    (hinge : OctahedralNet.hinges.Adj x y) :
    P.ShareEdge (graph.netFace small_faces source slit x) (graph.netFace small_faces source slit y) := by
  obtain ⟨a, b, different, common⟩ := Finset.card_eq_two.mp (OctahedralNet.hinge_common_card source slit x y hinge)
  change affineDimension (_ ∩ _) = 1
  rw [graph.intersection_eq_labeledHull, graph.netFace_labels small_faces octahedral,
    graph.netFace_labels small_faces octahedral, common, labeledHull]
  simp only [Finset.coe_pair, Set.image_insert_eq, Set.image_singleton, affineDimension_convexHull]
  exact affineDimension_pair (fun same => different (graph.vertex.injective (Subtype.ext same)))

include octahedral in
/-- An indexed common vertex pair identifies the entire original facet intersection. -/
theorem netFace_intersection_pair (source : Fin 6) (slit : Fin 4) (x y : OctahedralNet.FaceIndex) (a b : Fin 6)
    (common : OctahedralTriangles.vertices (OctahedralNet.triangle source slit x) ∩
      OctahedralTriangles.vertices (OctahedralNet.triangle source slit y) = {a, b}) :
    (graph.netFace small_faces source slit x).val ∩ (graph.netFace small_faces source slit y).val =
      segment ℝ (graph.vertex a : Space) (graph.vertex b) := by
  rw [graph.intersection_eq_labeledHull, graph.netFace_labels small_faces octahedral,
    graph.netFace_labels small_faces octahedral, common, labeledHull]
  simp only [Finset.coe_pair, Set.image_insert_eq, Set.image_singleton, convexHull_pair]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
