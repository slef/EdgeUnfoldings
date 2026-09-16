import SixVertexUnfolding.Geometry.EdgeSourceImages
import SixVertexUnfolding.Geometry.TerminalSourceData

/-! Actual terminal source copies in the joined development of two faces.
Targets on their shared edge are allowed, as are routes ending along it. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G)

/-- The final route portion is straight from this source in the joined edge development. -/
def HasTerminalSource (f : P.BoundaryCurve) (source : Plane) : Prop :=
  ∃ start : unitInterval, start < 1 ∧ ∀ t ∈ Icc start 1,
    (f t : Space) ∈ F.val ∪ G.val ∧
    chart.unfold (f t) = AffineMap.lineMap source (chart.unfold (f 1)) (t : ℝ)

/-- A first-face terminal source transfers to the joined coordinates. -/
theorem terminal_from_first (f : P.BoundaryCurve) (source : Plane)
    (terminal : P.HasTerminalSource f F source) : chart.HasTerminalSource f (chart.firstMotion source) := by
  have target := terminal.target_in_face
  obtain ⟨start, before, tail⟩ := terminal
  refine ⟨start, before, ?_⟩
  intro t ht
  have position := tail t ht
  refine ⟨Or.inl position.1, ?_⟩
  rw [chart.unfold_of_first position.1, chart.unfold_of_first target,
    ← chart.firstMotion_on_face _ position.1, position.2, AffineMap.apply_lineMap,
    chart.firstMotion_on_face _ target]

/-- A second-face terminal source transfers to the same joined coordinates. -/
theorem terminal_from_second (f : P.BoundaryCurve) (source : Plane)
    (terminal : P.HasTerminalSource f G source) : chart.HasTerminalSource f (chart.secondMotion source) := by
  have target := terminal.target_in_face
  obtain ⟨start, before, tail⟩ := terminal
  refine ⟨start, before, ?_⟩
  intro t ht
  have position := tail t ht
  refine ⟨Or.inr position.1, ?_⟩
  rw [chart.unfold_of_second position.1, chart.unfold_of_second target,
    ← chart.secondMotion_on_face _ position.1, position.2, AffineMap.apply_lineMap,
    chart.secondMotion_on_face _ target]

/-- The joined terminal source of a fixed route is unique, including on the crease. -/
theorem terminal_source_unique (f : P.BoundaryCurve) (p q : Plane)
    (first : chart.HasTerminalSource f p) (second : chart.HasTerminalSource f q) : p = q := by
  obtain ⟨s, s_before, first⟩ := first
  obtain ⟨u, u_before, second⟩ := second
  obtain ⟨t, after, before⟩ := exists_between (max_lt s_before u_before)
  exact lineMap_left_unique p q (chart.unfold (f 1)) t (show (t : ℝ) < 1 from before).ne
    ((first t ⟨(le_max_left s u).trans after.le, before.le⟩).2.symm.trans
      (second t ⟨(le_max_right s u).trans after.le, before.le⟩).2)

/-- A canonical geodesic whose target has only these incident faces has an actual source in their combined list. -/
theorem exists_terminal_source (graph : P.SixVertexGraph)
    (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (H.val ∩ (P.vertices : Set Space)).ncard = 4)
    (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves) (different : f 0 ≠ f 1)
    (only_two : ∀ H : P.Face, (f 1 : Space) ∈ H.val → H = F ∨ H = G) :
    ∃ source ∈ chart.sourceImages (f 0), chart.HasTerminalSource f source := by
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  obtain ⟨code, start, before, tail⟩ := (P.surfacePathOfCurve f).exists_terminal_source_code shortest finite speed
    (graph.shortest_lipschitz_avoids_vertices small_faces _ (fun h => different (Subtype.ext h)) shortest finite speed)
  have target := (tail 1 ⟨unitInterval.le_one', le_rfl⟩).1
  have terminal : P.HasTerminalSource f (code.face code.last) (code.sourceImage (f 0)) := ⟨start, before, tail⟩
  rcases only_two (code.face code.last) target with first | second
  · have member : code.sourceImage (f 0) ∈ P.sourceImages (f 0) F := ⟨⟨code, first⟩, rfl⟩
    refine ⟨chart.firstMotion (code.sourceImage (f 0)), Or.inl ⟨_, member, rfl⟩,
      chart.terminal_from_first f _ ?_⟩
    simpa only [first] using terminal
  · have member : code.sourceImage (f 0) ∈ P.sourceImages (f 0) G := ⟨⟨code, second⟩, rfl⟩
    refine ⟨chart.secondMotion (code.sourceImage (f 0)), Or.inr ⟨_, member, rfl⟩,
      chart.terminal_from_second f _ ?_⟩
    simpa only [second] using terminal

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
