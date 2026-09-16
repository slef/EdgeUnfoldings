import SixVertexUnfolding.Geometry.CutEdgeFaceSources
import SixVertexUnfolding.Geometry.CutEdgeHingeSources
import SixVertexUnfolding.Geometry.CutEdgeFacetType
import SixVertexUnfolding.Geometry.BisectorBaseTriangles

/-! Every cut-tree edge has a pair of planar metric triangles. Their
base length and all radial lengths are proved from the actual surface.
Identification of the full strips with these triangles is a further step. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A planar base and two source copies with the exact intrinsic radial distance profile. -/
structure CutEdgeMetricModel {P : ConvexPolyhedron} {a : frontier P.body}
    (T : P.CutLocusTree a) {u v : T.vertices} (edge : T.graph.Adj u v) where
  left : Plane
  right : Plane
  first : Plane
  second : Plane
  base_length : dist left right = dist (u : Space) (v : Space)
  distinct_sources : first ≠ second
  first_distances : ∀ t : unitInterval,
    dist first (AffineMap.lineMap left right (t : ℝ)) = P.surfaceDist a (T.closedEdgeTarget edge t)
  second_distances : ∀ t : unitInterval,
    dist second (AffineMap.lineMap left right (t : ℝ)) = P.surfaceDist a (T.closedEdgeTarget edge t)

namespace CutEdgeMetricModel

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
  {u v : T.vertices} {edge : T.graph.Adj u v} (M : CutEdgeMetricModel T edge)

theorem base_different : M.left ≠ M.right := by
  intro same
  have zero : dist (u : Space) (v : Space) = 0 := by rw [← M.base_length, same, dist_self]
  exact edge.ne (Subtype.ext (dist_eq_zero.mp zero))

theorem left_distances : dist M.first M.left = dist M.second M.left := by
  simpa using
    (M.first_distances 0).trans (M.second_distances 0).symm

theorem right_distances : dist M.first M.right = dist M.second M.right := by
  simpa using
    (M.first_distances 1).trans (M.second_distances 1).symm

/-- Neither planar triangle is degenerate. -/
theorem noncollinear : ¬ Collinear ℝ ({M.first, M.left, M.right} : Set Plane) ∧
    ¬ Collinear ℝ ({M.second, M.left, M.right} : Set Plane) :=
  ⟨bisector_base_noncollinear _ _ _ _ M.distinct_sources M.base_different M.left_distances M.right_distances,
    bisector_base_noncollinear _ _ _ _ M.distinct_sources.symm M.base_different M.left_distances.symm M.right_distances.symm⟩

/-- Construct the metric model in specified face or hinge coordinates. -/
noncomputable def fromAffineSources (place : Space →ᵃ[ℝ] Plane) (p q : Plane) (different : p ≠ q)
    (base_length : dist (place u) (place v) = dist (u : Space) (v : Space))
    (profiles : ∀ t : unitInterval,
      P.surfaceDist a (T.closedEdgeTarget edge t) = dist p (place (T.closedEdgeTarget edge t)) ∧
      P.surfaceDist a (T.closedEdgeTarget edge t) = dist q (place (T.closedEdgeTarget edge t))) :
    CutEdgeMetricModel T edge := by
  refine ⟨place u, place v, p, q, base_length, different, ?_, ?_⟩
  · intro t
    simpa only [← AffineMap.apply_lineMap] using (profiles t).1.symm
  · intro t
    simpa only [← AffineMap.apply_lineMap] using (profiles t).2.symm

/-- Affine coordinates of a face or joined hinge supply a metric model. -/
theorem of_affine_sources (place : Space →ᵃ[ℝ] Plane) (p q : Plane) (different : p ≠ q)
    (base_length : dist (place u) (place v) = dist (u : Space) (v : Space))
    (profiles : ∀ t : unitInterval,
      P.surfaceDist a (T.closedEdgeTarget edge t) = dist p (place (T.closedEdgeTarget edge t)) ∧
      P.surfaceDist a (T.closedEdgeTarget edge t) = dist q (place (T.closedEdgeTarget edge t))) :
    Nonempty (CutEdgeMetricModel T edge) := ⟨fromAffineSources place p q different base_length profiles⟩

theorem base_first_noncollinear : ¬ Collinear ℝ ({M.left, M.right, M.first} : Set Plane) := by
  rw [show ({M.left, M.right, M.first} : Set Plane) = {M.first, M.left, M.right} by
    ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto]
  exact M.noncollinear.1

theorem base_second_noncollinear : ¬ Collinear ℝ ({M.left, M.right, M.second} : Set Plane) := by
  rw [show ({M.left, M.right, M.second} : Set Plane) = {M.second, M.left, M.right} by
    ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto]
  exact M.noncollinear.2

end CutEdgeMetricModel

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Every actual cut-tree edge has its two metric triangles, including edges along original hinges. -/
theorem exists_cut_edge_metric_model (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) : Nonempty (CutEdgeMetricModel T edge) := by
  obtain ⟨S⟩ := graph.exists_cut_edge_strips small_faces a T edge
  rcases T.open_edge_facet_type edge with ⟨F, contained, unique⟩ | ⟨F, G, shared, contained⟩
  · obtain ⟨p, _, q, _, different, _, profiles⟩ := graph.cut_edge_face_sources small_faces a T edge S F unique
    apply CutEdgeMetricModel.of_affine_sources (P.faceCoordinates F) p q different ?_ profiles
    exact P.faceCoordinates_rigid F u (by simpa only [T.closedEdgeTarget_zero] using contained 0)
      v (by simpa only [T.closedEdgeTarget_one] using contained 1)
  · obtain ⟨center, inside⟩ := P.solid
    obtain ⟨facets⟩ := P.exists_normalized_facets inside
    obtain ⟨chart⟩ := exists_edge_folding facets F G shared
    obtain ⟨p, _, q, _, different, _, profiles⟩ := chart.cut_edge_hinge_sources graph small_faces shared a T edge S
      (fun t => contained (interiorTime t))
    apply CutEdgeMetricModel.of_affine_sources chart.left p q different ?_ profiles
    exact chart.left_rigid u (subset_affineSpan ℝ _ (by simpa only [T.closedEdgeTarget_zero] using (contained 0).1))
      v (subset_affineSpan ℝ _ (by simpa only [T.closedEdgeTarget_one] using (contained 1).1))

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
