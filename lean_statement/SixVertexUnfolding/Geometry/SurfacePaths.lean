import SixVertexUnfolding.Geometry.EdgeGraph

/-! Actual continuous paths on the polyhedral boundary, measured by Mathlib's total variation.
This supplies the shortest-path premise for straight original edges and face diagonals.
It makes no claim yet about nonoverlap of a star unfolding. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open scoped ENNReal NNReal

/-- A continuous path whose entire image lies on the boundary of the solid. -/
structure SurfacePath (P : ConvexPolyhedron) (a b : Space) where
  curve : Path a b
  on_surface : ∀ t, curve t ∈ frontier P.body

namespace SurfacePath

variable {P : ConvexPolyhedron} {a b : Space}

/-- Arc length, including infinite length, is the supremum of lengths of inscribed polygonal chains. -/
noncomputable def length (path : P.SurfacePath a b) : ℝ≥0∞ :=
  eVariationOn path.curve.extend (Set.Icc 0 1)

/-- Every continuous surface path is at least as long as the Euclidean chord joining its endpoints. -/
theorem chord_le_length (path : P.SurfacePath a b) : edist a b ≤ path.length := by
  have bound := eVariationOn.edist_le path.curve.extend
    (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
  simpa only [Path.extend_zero, Path.extend_one] using bound

/-- Shortest means no other continuous path on the surface has smaller arc length. -/
def IsShortest (path : P.SurfacePath a b) : Prop :=
  ∀ other : P.SurfacePath a b, path.length ≤ other.length

/-- A whole face contains the straight path between any two of its points. -/
noncomputable def inFace (F : P.Face) (ha : a ∈ F.val) (hb : b ∈ F.val) : P.SurfacePath a b where
  curve := Path.segment a b
  on_surface t := F.subset_frontier (F.convex.segment_subset ha hb (by
    rw [← Path.range_segment]
    exact ⟨t, rfl⟩))

/-- The straight face path has exactly the length of its Euclidean chord. -/
theorem inFace_length (F : P.Face) (ha : a ∈ F.val) (hb : b ∈ F.val) :
    (inFace F ha hb).length = edist a b := by
  apply le_antisymm ?_ (inFace F ha hb).chord_le_length
  change eVariationOn (Path.segment a b).extend (Set.Icc 0 1) ≤ edist a b
  rw [eVariationOn.congr (Path.eqOn_extend_segment a b)]
  have unit : eVariationOn (id : ℝ → ℝ) (Set.Icc 0 1) ≤ 1 := by
    simpa using (monotone_id.monotoneOn (s := Set.univ)).eVariationOn_le
      (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
  have bound := (lipschitzWith_lineMap a b (𝕜 := ℝ)).lipschitzOnWith.comp_eVariationOn_le
    (show Set.MapsTo (id : ℝ → ℝ) (Set.Icc 0 1) Set.univ from fun _ _ => Set.mem_univ _)
  exact bound.trans (by simpa using mul_le_mul_right unit (nndist a b : ℝ≥0∞))

/-- Straight paths within a face minimize length among all continuous surface paths. -/
theorem inFace_shortest (F : P.Face) (ha : a ∈ F.val) (hb : b ∈ F.val) :
    (inFace F ha hb).IsShortest := by
  intro other
  rw [inFace_length]
  exact other.chord_le_length

end SurfacePath

/-- Every original edge is realized by a shortest surface path with exactly that edge as its image. -/
theorem edge_has_shortest_surface_path (P : ConvexPolyhedron) (a b : P.Vertex)
    (edge : P.edgeGraph.Adj a b) :
    ∃ path : P.SurfacePath a b, path.IsShortest ∧
      Set.range path.curve = segment ℝ (a : Space) (b : Space) := by
  obtain ⟨_, F, G, _, common⟩ := edge
  have aF : (a : Space) ∈ F.val :=
    (common ▸ (left_mem_segment ℝ (a : Space) (b : Space))).1
  have bF : (b : Space) ∈ F.val :=
    (common ▸ (right_mem_segment ℝ (a : Space) (b : Space))).1
  exact ⟨SurfacePath.inFace F aF bF, SurfacePath.inFace_shortest F aF bF, Path.range_segment _ _⟩

end SixVertexUnfolding.ConvexPolyhedron
