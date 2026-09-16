import SixVertexUnfolding.Geometry.CommonFacetVertices
import SixVertexUnfolding.Geometry.QuadrilateralEdges

/-! Label the vertices of whole original facets by the six original vertex labels. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (index : Fin 6 ≃ P.Vertex)

/-- The labels of the original vertices belonging to this whole facet. -/
noncomputable def vertexLabels (F : P.Face) : Finset (Fin 6) := by
  classical
  exact Finset.univ.filter (fun i => (index i : Space) ∈ F.val)

@[simp] theorem mem_vertexLabels (F : P.Face) (i : Fin 6) :
    i ∈ F.vertexLabels index ↔ (index i : Space) ∈ F.val := by
  classical
  simp [vertexLabels]

/-- Reading the labels as spatial vertices recovers exactly the facet's original vertices. -/
theorem image_vertexLabels (F : P.Face) :
    (fun i => (index i : Space)) '' (F.vertexLabels index : Set (Fin 6)) =
      F.val ∩ (P.vertices : Set Space) := by
  ext x
  constructor
  · rintro ⟨i, member, rfl⟩
    exact ⟨(F.mem_vertexLabels index i).mp member, (index i).property⟩
  · rintro ⟨on_face, vertex⟩
    let v : P.Vertex := ⟨x, vertex⟩
    refine ⟨index.symm v, ?_, ?_⟩
    · simpa using on_face
    · simp [v]

/-- Counting labels is the same as counting genuine vertices of the original facet. -/
theorem vertexLabels_card (F : P.Face) :
    (F.vertexLabels index).card = (F.val ∩ (P.vertices : Set Space)).ncard := by
  rw [← F.image_vertexLabels index]
  rw [Set.ncard_image_of_injective _ (fun i j same => index.injective (Subtype.ext same))]
  simp only [Set.ncard_coe_finset]

/-- Whole original facets are determined by their vertex labels. -/
theorem vertexLabels_injective : Function.Injective (fun F : P.Face => F.vertexLabels index) := by
  intro F G same
  change F.vertexLabels index = G.vertexLabels index at same
  apply F.eq_of_same_vertices G
  rw [← F.image_vertexLabels index, ← G.image_vertexLabels index, same]

/-- Two distinct nonadjacent labels occur together in at most one whole facet. -/
theorem eq_of_common_nonedge_labels (F G : P.Face) (i j : Fin 6) (different : i ≠ j)
    (nonedge : ¬ P.edgeGraph.Adj (index i) (index j))
    (iF : i ∈ F.vertexLabels index) (jF : j ∈ F.vertexLabels index)
    (iG : i ∈ G.vertexLabels index) (jG : j ∈ G.vertexLabels index) : F = G :=
  F.eq_of_common_nonedge G (index i) (index j) (index.injective.ne different) nonedge
    ((F.mem_vertexLabels index i).mp iF) ((F.mem_vertexLabels index j).mp jF)
    ((G.mem_vertexLabels index i).mp iG) ((G.mem_vertexLabels index j).mp jG)

end SixVertexUnfolding.ConvexPolyhedron.Face
