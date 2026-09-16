import SixVertexUnfolding.Geometry.LocalFormulaIdentifiesSource
import SixVertexUnfolding.Geometry.SourceFormulaExtension
import SixVertexUnfolding.Geometry.ShortestExtensionUniqueness

/-! Every actual terminal source supplies real competing routes to all
nearby points of its target face. A unique proper prefix supplies the
local distance formula, so no full-route perturbation is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set Filter
open scoped Topology

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Each actual terminal source is realized by exact-length surface competitors throughout a target neighborhood. -/
theorem terminal_source_competitors (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (F : P.Face) (unique_face : ∀ G : P.Face, (f 1 : Space) ∈ G.val → G = F)
    (source : Plane) (terminal : P.HasTerminalSource f F source) :
    ∃ V : Set Space, IsOpen V ∧ (f 1 : Space) ∈ V ∩ F.val ∧ ∀ x ∈ V ∩ F.val,
      ∃ path : P.SurfacePath (f 0) x, path.length ≠ ⊤ ∧ path.length.toReal = dist source (P.faceCoordinates F x) := by
  let path := P.surfacePathOfCurve f
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  obtain ⟨start, start_before, tail⟩ := terminal
  have terminal' : P.HasTerminalSource f F source := ⟨start, start_before, tail⟩
  obtain ⟨O, openO, targetO, covers⟩ := P.unique_face_neighborhood F unique_face
  have near : ∀ᶠ r : ℝ in 𝓝 1, path.curve.extend r ∈ O :=
    path.curve.continuous_extend.continuousAt.eventually (openO.mem_nhds (by simpa using targetO))
  have late : ∀ᶠ r : ℝ in 𝓝 1, (start : ℝ) < r := Ioi_mem_nhds start_before
  obtain ⟨r, before, after, inO⟩ := (late.and near).exists_lt
  let m : unitInterval := ⟨r, (start.property.1.trans_lt after).le, before.le⟩
  have positive : 0 < m := start.property.1.trans_lt after
  have fmO : (f m : Space) ∈ O := by
    change path.curve.extend (m : ℝ) ∈ O at inO
    rw [Path.extend_apply path.curve m.property] at inO
    exact inO
  have unique_m := (covers _ ⟨fmO, (f m).property⟩).2
  have distinct_m : f 0 ≠ f m := by
    intro same
    exact positive.ne ((path.shortest_lipschitz_injective
      (fun h => different (Subtype.ext h)) shortest finite speed) (congrArg Subtype.val same))
  have prefix_unique := graph.geodesic_interior_targets_unique small_faces f geodesic different m before
  obtain ⟨other, _, U, openU, fmU, formula⟩ := graph.unique_route_source_distance small_faces
    (f 0) (f m) distinct_m F unique_m prefix_unique
  have same := P.local_formula_identifies_source f geodesic F source other terminal' start tail
    m after.le positive before U openU fmU formula
  subst other
  have at_m := tail m ⟨after.le, before.le⟩
  exact P.source_formula_extension (f 0).property F at_m.1 terminal'.target_in_face unique_m source m
    positive before at_m.2 U openU fmU formula

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
