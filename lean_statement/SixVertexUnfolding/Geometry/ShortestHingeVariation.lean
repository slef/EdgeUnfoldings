import SixVertexUnfolding.Geometry.ShortestSubpaths
import SixVertexUnfolding.Geometry.HingeFirstVariation

/-! Actual shortest surface paths minimize the length obtained by moving a
crossing along a common face edge. Convexity supplies every competitor. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set Filter
open scoped ENNReal NNReal Topology

variable {P : ConvexPolyhedron} {a b : Space}

/-- A portion splits additively at any intermediate parameter. -/
theorem portion_length_split (path : P.SurfacePath a b) (s m t : unitInterval)
    (sm : s ≤ m) (mt : m ≤ t) :
    (path.portion s t (sm.trans mt)).length =
      (path.portion s m sm).length + (path.portion m t mt).length := by
  simp only [portion_length]
  simpa only [univ_inter] using
    (eVariationOn.Icc_add_Icc path.curve (s := Set.univ) sm mt (mem_univ m)).symm

/-- A shortest path's two-face crossing minimizes the sum of its two chord lengths. -/
theorem shortest_hinge_length_minimum (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (F G : P.Face) (s m t : unitInterval)
    (sm : s ≤ m) (mt : m ≤ t) (hs : path.curve s ∈ F.val)
    (hm : path.curve m ∈ F.val ∩ G.val) (ht : path.curve t ∈ G.val)
    (w : Space) (hw : w ∈ F.val ∩ G.val) :
    dist (path.curve s) (path.curve m) + dist (path.curve m) (path.curve t) ≤
      dist (path.curve s) w + dist w (path.curve t) := by
  let competitor := (inFace F hs hw.1).join (inFace G hw.2 ht)
  have comparison := path.portion_shortest shortest finite s t (sm.trans mt) competitor
  rw [path.portion_length_split s m t sm mt,
    (path.portion s m sm).shortest_cofacial_length
      (path.portion_shortest shortest finite s m sm) F hs hm.1,
    (path.portion m t mt).shortest_cofacial_length
      (path.portion_shortest shortest finite m t mt) G hm.2 ht] at comparison
  change _ ≤ ((inFace F hs hw.1).join (inFace G hw.2 ht)).length at comparison
  rw [join_length, inFace_length, inFace_length] at comparison
  simp only [edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at comparison
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg dist_nonneg dist_nonneg)).mp comparison

/-- At a crossing in the open common edge, the incoming and outgoing hinge components cancel. -/
theorem shortest_hinge_stationary (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (F G : P.Face) (s m t : unitInterval)
    (sm : s ≤ m) (mt : m ≤ t) (hs : path.curve s ∈ F.val)
    (hm : path.curve m ∈ F.val ∩ G.val) (ht : path.curve t ∈ G.val)
    (different_left : path.curve s ≠ path.curve m) (different_right : path.curve t ≠ path.curve m)
    (p q : Space) (hp : p ∈ F.val ∩ G.val) (hq : q ∈ F.val ∩ G.val)
    (inside_edge : path.curve m ∈ openSegment ℝ p q) :
    inner ℝ (q - p) (path.curve s - path.curve m) / ‖path.curve s - path.curve m‖ +
      inner ℝ (q - p) (path.curve t - path.curve m) / ‖path.curve t - path.curve m‖ = 0 := by
  apply hinge_distance_stationary _ _ _ _ different_left different_right
  rw [openSegment_eq_image_lineMap] at inside_edge
  obtain ⟨r, hr, location⟩ := inside_edge
  have variation (u : ℝ) : u • (q - p) + path.curve m = AffineMap.lineMap p q (r + u) := by
    rw [← location]
    simp only [AffineMap.lineMap_apply_module']
    module
  have nearby : ∀ᶠ u : ℝ in 𝓝 0, r + u ∈ Ioo 0 1 :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      (by simpa using isOpen_Ioo.mem_nhds hr)
  filter_upwards [nearby] with u hu
  have segment_point : AffineMap.lineMap p q (r + u) ∈ segment ℝ p q := by
    rw [segment_eq_image_lineMap]
    exact ⟨r + u, ⟨hu.1.le, hu.2.le⟩, rfl⟩
  have shared : u • (q - p) + path.curve m ∈ F.val ∩ G.val := by
    rw [variation]
    exact ⟨F.convex.segment_subset hp.1 hq.1 segment_point,
      G.convex.segment_subset hp.2 hq.2 segment_point⟩
  have minimum := path.shortest_hinge_length_minimum shortest finite F G s m t sm mt hs hm ht _ shared
  simpa only [zero_smul, zero_add, dist_comm (path.curve t)] using minimum

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
