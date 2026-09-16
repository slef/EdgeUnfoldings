import SixVertexUnfolding.Geometry.EdgeActiveSourceRoutes
import SixVertexUnfolding.Geometry.EdgeLocalSourceIdentification

/-! A local single-source formula in joined coordinates forces one actual
shortest route, including at a target on an original edge. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch

open Set

variable {P : ConvexPolyhedron} {center z : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} {chart : EdgeFolding facets F G} (patch : chart.MetricPatch z)
  (graph : P.SixVertexGraph)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- A local source formula identifies the terminal source of every actual route ending there. -/
theorem terminal_source_of_local_formula (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (target : (f 1 : Space) ∈ patch.domain)
    (source : Plane) (U : Set Space) (openU : IsOpen U) (targetU : (f 1 : Space) ∈ U)
    (formula : ∀ x ∈ U ∩ frontier P.body, P.surfaceDist (f 0) x = dist source (chart.unfold x)) :
    chart.HasTerminalSource f source := by
  obtain ⟨actual, _, terminal⟩ := chart.exists_terminal_source graph small_faces f geodesic different (patch.only_two _ target)
  let path := P.surfacePathOfCurve f
  obtain ⟨m, positive, before, inside, _⟩ := path.common_time_near_target path (U ∩ patch.domain)
    (openU.inter patch.open_domain) ⟨targetU, target⟩
  have same := patch.local_formula_identifies_source f geodesic actual source terminal target
    m positive before inside.2 U openU inside.1 formula
  rw [same]
  exact terminal

include graph small_faces in
/-- A local planar source-distance formula forces uniqueness of the actual route. -/
theorem unique_route_of_local_source_formula (a b : frontier P.body) (different : a ≠ b)
    (target : (b : Space) ∈ patch.domain) (source : Plane) (U : Set Space) (openU : IsOpen U) (bU : (b : Space) ∈ U)
    (formula : ∀ x ∈ U ∩ frontier P.body, P.surfaceDist a x = dist source (chart.unfold x)) :
    (P.geodesicFiber a b).Subsingleton := by
  have terminal (f : P.BoundaryCurve) (hf : f ∈ P.geodesicFiber a b) : chart.HasTerminalSource f source := by
    have first : f 0 = a := congrArg Prod.fst hf.2
    have last : f 1 = b := congrArg Prod.snd hf.2
    exact patch.terminal_source_of_local_formula graph small_faces f hf.1
      (by simpa only [first, last] using different) (by simpa only [last] using target) source U openU
      (by simpa only [last] using bU) (by simpa only [first] using formula)
  intro f hf g hg
  have first : f 0 = a := congrArg Prod.fst hf.2
  have last : f 1 = b := congrArg Prod.snd hf.2
  exact chart.routes_agree_of_terminal_source graph small_faces f g hf.1 hg.1
    (by simpa only [first, last] using different)
    ((congrArg Prod.fst hf.2).trans (congrArg Prod.fst hg.2).symm)
    ((congrArg Prod.snd hf.2).trans (congrArg Prod.snd hg.2).symm) source (terminal f hf) (terminal g hg)

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch
