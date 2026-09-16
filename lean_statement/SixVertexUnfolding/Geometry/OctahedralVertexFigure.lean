import SixVertexUnfolding.Geometry.OctahedralCoverage
import SixVertexUnfolding.Geometry.VertexFigureEdges
import SixVertexUnfolding.Geometry.FourRayFan
import SixVertexUnfolding.OctahedralFans

/-! The four incident subdivision directions form an actual supported convex vertex figure. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph) (v : Fin 6)
    (figure : P.VertexFigure (graph.vertex v))

/-- The four incident directions, cut by the strictly supporting transverse plane. -/
noncomputable def fanRay (i : Fin 4) : Space := figure.direction (graph.vertex (fanNeighbor v i))

theorem fan_neighbor_distinct (i : Fin 4) :
    (graph.vertex (fanNeighbor v i) : Space) ≠ (graph.vertex v : Space) :=
  fun same => fanNeighbor_ne_source v i (graph.vertex.injective (Subtype.ext same))

/-- Each actual vertex-figure corner is among these four directions, since the opposite pair is a nonedge. -/
theorem figure_corners_subset_fan : figure.corners ⊆ Set.range (graph.fanRay v figure) := by
  intro x corner
  obtain ⟨w, adjacent, same⟩ := figure.corner_is_neighbor corner
  obtain ⟨label, rfl⟩ := graph.vertex.surjective w
  have different : label ≠ v := fun equality => adjacent.ne (by rw [equality])
  have not_opposite : label ≠ opposite v := by
    intro equality
    apply opposite_nonedge graph.kind v
    exact (graph.edges v (opposite v)).mp (equality ▸ adjacent)
  obtain ⟨i, equal⟩ := fanNeighbor_exhaust v label different not_opposite
  exact ⟨i, by simpa only [fanRay, equal] using same⟩

/-- The four selected rays span all three spatial directions. -/
theorem fanRay_spans : Submodule.span ℝ (Set.range (graph.fanRay v figure)) = ⊤ := by
  apply top_unique
  rw [← figure.corners_span]
  exact Submodule.span_mono (graph.figure_corners_subset_fan v figure)

theorem fanRay_injective : Function.Injective (graph.fanRay v figure) := by
  intro i j same
  have points := figure.direction_injective
    ⟨(graph.vertex (fanNeighbor v i)).property, graph.fan_neighbor_distinct v i⟩
    ⟨(graph.vertex (fanNeighbor v j)).property, graph.fan_neighbor_distinct v j⟩ same
  exact fanNeighbor_injective v (graph.vertex.injective (Subtype.ext points))

variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

/-- The source and successive neighboring vertices all lie on the assigned original facet. -/
theorem fan_sector_on_face (i : Fin 4) (j : Fin 6)
    (member : j ∈ ({v, fanNeighbor v i, fanNeighbor v (i + 1)} : Finset (Fin 6))) :
    (graph.vertex j : Space) ∈ (graph.triangleFace small_faces (fanTriangle v i)).val := by
  apply (Face.mem_vertexLabels graph.vertex _ j).mp
  rw [graph.triangleFace_labels]
  apply vertices_subset_carrier _ _
  rwa [fanTriangle_vertices]

include small_faces in
/-- Original supporting facet normals give the four supporting sides of the transverse figure. -/
theorem fan_side_exists (i : Fin 4) : ∃ normal : Space,
    normal ≠ 0 ∧ inner ℝ normal (graph.fanRay v figure i) = 0 ∧
      inner ℝ normal (graph.fanRay v figure (i + 1)) = 0 ∧
      ∀ j, inner ℝ normal (graph.fanRay v figure j) ≤ 0 := by
  let F := graph.triangleFace small_faces (fanTriangle v i)
  obtain ⟨_, normal, level, nonzero, support, face_eq⟩ := F.property
  have source_mem : (graph.vertex v : Space) ∈ F.val := graph.fan_sector_on_face v small_faces i v (by simp)
  have source_level : inner ℝ normal (graph.vertex v : Space) = level := (face_eq ▸ source_mem).2
  have difference (j : Fin 4) : inner ℝ normal (graph.fanRay v figure j) =
      (figure.gap (graph.vertex (fanNeighbor v j)))⁻¹ *
        (inner ℝ normal (graph.vertex (fanNeighbor v j) : Space) - level) := by
    rw [fanRay, VertexFigure.direction, inner_smul_right, inner_sub_right, source_level]
  have on_side (j : Fin 4) (member : (graph.vertex (fanNeighbor v j) : Space) ∈ F.val) :
      inner ℝ normal (graph.fanRay v figure j) = 0 := by
    have at_level : inner ℝ normal (graph.vertex (fanNeighbor v j) : Space) = level := (face_eq ▸ member).2
    rw [difference, at_level, sub_self, mul_zero]
  refine ⟨normal, nonzero, on_side i ?_, on_side (i + 1) ?_, ?_⟩
  · exact graph.fan_sector_on_face v small_faces i _ (by simp)
  · exact graph.fan_sector_on_face v small_faces i _ (by simp)
  · intro j
    rw [difference]
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact inv_nonneg.mpr (figure.gap_pos (graph.vertex (fanNeighbor v j)).property
        (graph.fan_neighbor_distinct v j)).le
    · exact sub_nonpos.mpr (support _ (P.vertices_subset_body (graph.vertex (fanNeighbor v j)).property))

/-- The geometric vertex figure satisfies the four-ray model, including flat auxiliary corners. -/
noncomputable def vertexFan : FourRayFan := by
  classical
  choose normal nonzero left right bound using graph.fan_side_exists v figure small_faces
  refine {
    ray := graph.fanRay v figure
    distinct := graph.fanRay_injective v figure
    height := -(innerSL ℝ figure.normal).toLinearMap
    level := ?_
    spans := graph.fanRay_spans v figure
    side := fun i => (innerSL ℝ (normal i)).toLinearMap
    side_nonzero := ?_
    side_left := left
    side_right := right
    side_bound := bound
  }
  · intro i
    change -(inner ℝ figure.normal (figure.direction (graph.vertex (fanNeighbor v i)))) = 1
    rw [figure.direction_height (graph.vertex (fanNeighbor v i)).property (graph.fan_neighbor_distinct v i)]
    norm_num
  · intro i zero
    have self_zero := congrArg (fun f : Space →ₗ[ℝ] ℝ => f (normal i)) zero
    change inner ℝ (normal i) (normal i) = 0 at self_zero
    rw [real_inner_self_eq_norm_sq] at self_zero
    exact nonzero i (norm_eq_zero.mp (sq_eq_zero_iff.mp self_zero))

@[simp] theorem vertexFan_ray (i : Fin 4) :
    (graph.vertexFan v figure small_faces).ray i = graph.fanRay v figure i := rfl

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
