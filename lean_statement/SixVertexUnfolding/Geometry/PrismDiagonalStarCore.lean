import SixVertexUnfolding.Geometry.PrismDiagonalFallback
import SixVertexUnfolding.Geometry.CofacialStarEmbedding
import SixVertexUnfolding.Geometry.RetainedHingeAgreement
import SixVertexUnfolding.Geometry.FaceInteriorUniqueness

/-! The four whole faces A-C-E-F survive the cofacial star at vertex 2.
Their three retained hinges are exactly the corresponding fallback hinges, so
the star provides a rigid, joined, nonoverlapping placement of this chain. -/

namespace SixVertexUnfolding.Prism

open FaceLabel

def starCore : Finset FaceLabel := {A, C, E, F}

end SixVertexUnfolding.Prism

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set Prism Prism.FaceLabel

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- Manuscript vertex 2, as a point on the actual surface. -/
noncomputable def prismStarSource : frontier P.body :=
  ⟨graph.prismVertex 2, P.vertex_mem_frontier (graph.prismVertex 2).property⟩

variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)
variable (prism_kind : graph.kind = .prismDiagonal)
include prism_kind

/-- All cuts from vertex 2 lie in the two quadrilateral faces. -/
theorem prism_star_cuts_in_quadrilaterals (b : frontier P.body)
    (cut : b ∈ P.starCuts graph.prismStarSource) :
    (b : Space) ∈ (graph.prismDiagonalFace small_faces B).val ∪
      (graph.prismDiagonalFace small_faces D).val := by
  obtain ⟨v, between⟩ := cut
  obtain ⟨i, rfl⟩ := (vertexLabel.trans graph.vertex).surjective v
  obtain ⟨f, quad, source, target⟩ := (by decide : ∀ i : Fin 6,
    ∃ f, (f = B ∨ f = D) ∧ 2 ∈ faceVertices f ∧ i ∈ faceVertices f) i
  have inside : (b : Space) ∈ (graph.prismDiagonalFace small_faces f).val :=
    (graph.prismDiagonalFace small_faces f).convex.segment_subset
      ((graph.prismVertex_mem_face small_faces prism_kind f 2).mpr source)
      ((graph.prismVertex_mem_face small_faces prism_kind f i).mpr target) between
  rcases quad with rfl | rfl
  exacts [Or.inl inside, Or.inr inside]

/-- The interiors of A, C, E, F contain none of the star's cuts. -/
theorem prism_star_core_uncut (f : FaceLabel) (core : f ∈ starCore)
    (x : Space) (hx : x ∈ (graph.prismDiagonalFace small_faces f).val)
    (inside : P.faceCoordinates (graph.prismDiagonalFace small_faces f) x ∈
      interior (P.faceCoordinates (graph.prismDiagonalFace small_faces f) ''
        (graph.prismDiagonalFace small_faces f).val)) :
    (⟨x, (graph.prismDiagonalFace small_faces f).subset_frontier hx⟩ : frontier P.body) ∉
      P.starCuts graph.prismStarSource := by
  intro cut
  have member := graph.prism_star_cuts_in_quadrilaterals small_faces prism_kind _ cut
  have absent := (by decide : ∀ f, f ∈ starCore → f ≠ B ∧ f ≠ D) f core
  have unique (g : FaceLabel) (hg : x ∈ (graph.prismDiagonalFace small_faces g).val) : f = g :=
    (graph.prismDiagonalFace_bijective small_faces prism_kind).1
      ((graph.prismDiagonalFace small_faces f).unique_of_placed_interior
        (graph.prismDiagonalFace small_faces g) _ (P.faceCoordinates_rigid _) hx inside hg)
  exact member.elim (fun h => absent.1 (unique B h)) (fun h => absent.2 (unique D h))

/-- The chain's three original hinges survive the cuts from vertex 2. -/
theorem prism_star_core_hinge_retained (f g : FaceLabel)
    (f_core : f ∈ starCore) (g_core : g ∈ starCore) (edge : fallbackHinges.Adj f g) :
    (P.retainedFaceGraph graph.prismStarSource).Adj
      (graph.prismDiagonalFace small_faces f) (graph.prismDiagonalFace small_faces g) := by
  let F := graph.prismDiagonalFace small_faces f
  let G := graph.prismDiagonalFace small_faces g
  have different : F ≠ G := (graph.prismDiagonalFace_bijective small_faces prism_kind).1.ne edge.ne
  obtain ⟨u, hu, v, hv, distinct, intersection⟩ :=
    F.shared_edge_endpoints G (graph.prism_fallback_original_hinge small_faces prism_kind f g edge)
  let x := midpoint ℝ u v
  have common : x ∈ F.val ∩ G.val := by rw [intersection]; exact midpoint_mem_segment _ _
  have nonvertex : x ∉ P.vertices := by
    intro vertex
    rcases P.vertex_in_segment_is_endpoint vertex (P.vertices_subset_body hu)
      (P.vertices_subset_body hv) (midpoint_mem_segment (𝕜 := ℝ) u v) with left | right
    · exact distinct ((left_eq_midpoint_iff ℝ).mp left)
    · exact distinct ((right_eq_midpoint_iff ℝ).mp right)
  have uncut : (⟨x, F.subset_frontier common.1⟩ : frontier P.body) ∉
      P.starCuts graph.prismStarSource := by
    intro cut
    have first := starCut_face_contains_source graph.prismStarSource _ F common.1 nonvertex cut
    have second := starCut_face_contains_source graph.prismStarSource _ G common.2 nonvertex cut
    have labels : 2 ∈ faceVertices f ∧ 2 ∈ faceVertices g :=
      ⟨(graph.prismVertex_mem_face small_faces prism_kind f 2).mp first,
        (graph.prismVertex_mem_face small_faces prism_kind g 2).mp second⟩
    exact (by decide : ∀ f g, f ∈ starCore → g ∈ starCore → fallbackHinges.Adj f g →
      ¬ (2 ∈ faceVertices f ∧ 2 ∈ faceVertices g)) f g f_core g_core edge labels
  exact ⟨different, ⟨⟨x, F.subset_frontier common.1⟩, uncut⟩, common⟩

/-- The proved cofacial star supplies all six pair separations in the four-face chain.
The unused placements of B and D are replaced by outward attachments later. -/
theorem exists_prism_star_core :
    ∃ place : FaceLabel → Space →ᵃ[ℝ] Plane,
      (∀ f, ∀ x ∈ (graph.prismDiagonalFace small_faces f).val,
        ∀ y ∈ (graph.prismDiagonalFace small_faces f).val, dist (place f x) (place f y) = dist x y) ∧
      (∀ f ∈ starCore, ∀ g ∈ starCore, f ≠ g →
        Disjoint (interior (place f '' (graph.prismDiagonalFace small_faces f).val))
          (interior (place g '' (graph.prismDiagonalFace small_faces g).val))) ∧
      (∀ f ∈ starCore, ∀ g ∈ starCore, fallbackHinges.Adj f g →
        EqOn (place f) (place g)
          ((graph.prismDiagonalFace small_faces f).val ∩ (graph.prismDiagonalFace small_faces g).val)) := by
  classical
  have cofacial := graph.prism_cofacial_sources small_faces prism_kind 2 (Or.inr (Or.inl rfl))
  obtain ⟨develop, embedding, _, _, _, metric⟩ := graph.cofacial_star_embedding small_faces
    graph.prismStarSource (vertexLabel 2) rfl cofacial
  have each_face (f : FaceLabel) : ∃ place : Space →ᵃ[ℝ] Plane,
      (∀ x ∈ (graph.prismDiagonalFace small_faces f).val,
        ∀ y ∈ (graph.prismDiagonalFace small_faces f).val, dist (place x) (place y) = dist x y) ∧
      (f ∈ starCore → ∀ b : P.UncutSurface graph.prismStarSource,
        (b.val : Space) ∈ (graph.prismDiagonalFace small_faces f).val → place b.val = develop b) := by
    by_cases core : f ∈ starCore
    · obtain ⟨place, rigid, agrees⟩ := uncut_face_rigid_placement develop metric
        (graph.prismDiagonalFace small_faces f) (graph.prism_star_core_uncut small_faces prism_kind f core)
      exact ⟨place, rigid, fun _ => (graph.prismDiagonalFace small_faces f).agrees_on_retained_face
        develop place agrees⟩
    · obtain ⟨place, rigid⟩ := (graph.prismDiagonalFace small_faces f).exists_rigid_placement
      exact ⟨place, rigid, fun h => (core h).elim⟩
  choose place rigid agrees using each_face
  refine ⟨place, rigid, ?_, ?_⟩
  · intro f hf g hg different
    exact uncut_face_placements_nonoverlap develop embedding.injective _ _
      ((graph.prismDiagonalFace_bijective small_faces prism_kind).1.ne different)
      (place f) (place g) (rigid f) (rigid g)
      (graph.prism_star_core_uncut small_faces prism_kind f hf)
      (graph.prism_star_core_uncut small_faces prism_kind g hg) (agrees f hf) (agrees g hg)
  · intro f hf g hg edge
    exact retained_hinge_agreement develop _ _ (place f) (place g) (agrees f hf) (agrees g hg)
      (graph.prism_star_core_hinge_retained small_faces prism_kind f g hf hg edge)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
