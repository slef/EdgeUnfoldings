import SixVertexUnfolding.Geometry.EmbeddedGraphStars
import SixVertexUnfolding.Geometry.CutArcTopology

/-! A length-preserving cut arc passes through its center in two directions.
It cannot end at a graph leaf, whose nearby trace lies on one cofacial ray. -/

namespace SixVertexUnfolding

open Set

/-- Distance from the first endpoint identifies a point of a spatial segment. -/
theorem space_segment_point_unique (a b x y : Space)
    (hx : x ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    (same_distance : dist a x = dist a y) : x = y := by
  by_cases same : a = b
  · rw [same, segment_same, mem_singleton_iff] at hx hy
    exact hx.trans hy.symm
  obtain ⟨s, hs, rfl⟩ := mem_segment_iff_wbtw.mp hx
  obtain ⟨t, ht, rfl⟩ := mem_segment_iff_wbtw.mp hy
  rw [dist_left_lineMap, dist_left_lineMap, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hs.1, abs_of_nonneg ht.1] at same_distance
  rw [mul_right_cancel₀ (dist_ne_zero.mpr same) same_distance]

namespace ConvexPolyhedron.CutArc

variable {P : ConvexPolyhedron} {a b : Space} (arc : P.CutArc a b)

include arc in
/-- No neighborhood of the center of a cut arc is confined to a cofacial segment starting there. -/
theorem not_one_sided (c : Space) (F : P.Face)
    (cofacial : segment ℝ b c ⊆ F.val) (U : Set Space) (openU : IsOpen U) (bU : b ∈ U)
    (one_sided : ∀ t ∈ Ioo (-arc.radius) arc.radius,
      arc.curve t ∈ U → arc.curve t ∈ segment ℝ b c) : False := by
  obtain ⟨δ, positive, near⟩ := Metric.isOpen_iff.mp
    (openU.preimage arc.continuous) 0 (by simpa only [mem_preimage, arc.at_zero] using bU)
  let t := min arc.radius δ / 2
  have t_pos : 0 < t := half_pos (lt_min arc.positive positive)
  have t_radius : t < arc.radius := by
    have := min_le_left arc.radius δ
    dsimp [t]
    linarith [arc.positive]
  have t_delta : t < δ := by
    have := min_le_right arc.radius δ
    dsimp [t]
    linarith
  have first : t ∈ Ioo (-arc.radius) arc.radius := ⟨by linarith [arc.positive], t_radius⟩
  have second : -t ∈ Ioo (-arc.radius) arc.radius := ⟨by linarith, by linarith [arc.positive]⟩
  have at_center : (0 : ℝ) ∈ Ioo (-arc.radius) arc.radius := ⟨by linarith [arc.positive], arc.positive⟩
  have forward : arc.curve t ∈ segment ℝ b c := one_sided t first (near (by
    change dist t 0 < δ
    simpa only [Real.dist_eq, sub_zero, abs_of_pos t_pos] using t_delta))
  have backward : arc.curve (-t) ∈ segment ℝ b c := one_sided (-t) second (near (by
    change dist (-t) 0 < δ
    simpa only [Real.dist_eq, sub_zero, abs_neg, abs_of_pos t_pos] using t_delta))
  have bF : b ∈ F.val := cofacial (left_mem_segment ℝ b c)
  have distances : dist b (arc.curve t) = dist b (arc.curve (-t)) := by
    rw [← P.surfaceDist_eq_dist_in_face F bF (cofacial forward),
      ← P.surfaceDist_eq_dist_in_face F bF (cofacial backward)]
    have left_distance := arc.distance 0 at_center t first
    have right_distance := arc.distance 0 at_center (-t) second
    simp only [arc.at_zero, Real.dist_eq, zero_sub, abs_neg, neg_neg] at left_distance right_distance
    exact left_distance.trans right_distance.symm
  have same := space_segment_point_unique b c _ _ forward backward distances
  have equal := arc.injective first second same
  linarith

end ConvexPolyhedron.CutArc

namespace ConvexPolyhedron.EmbeddedCutGraph

variable {P : ConvexPolyhedron} {a : frontier P.body} (K : P.EmbeddedCutGraph a)

include K in
/-- A graph vertex carrying a genuine two-sided cut arc cannot have just one neighbor. -/
theorem cut_arc_not_leaf (u v : K.vertices) (edge : K.graph.Adj u v)
    (arc : P.CutArc a u) (only_neighbor : ∀ w, K.graph.Adj u w → w = v) : False := by
  obtain ⟨U, openU, uU, local_segment⟩ := K.leaf_segment_neighborhood u v only_neighbor
  obtain ⟨F, cofacial⟩ := K.cofacial_edges u v edge
  apply arc.not_one_sided v F cofacial U openU uU
  intro t ht near
  apply local_segment ⟨near, ?_⟩
  exact ⟨⟨arc.curve t, arc.on_surface t ht⟩, Or.inl (arc.on_cut t ht), rfl⟩

end ConvexPolyhedron.EmbeddedCutGraph
end SixVertexUnfolding
