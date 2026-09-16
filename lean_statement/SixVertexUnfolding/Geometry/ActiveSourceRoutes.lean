import SixVertexUnfolding.Geometry.ActiveSources
import SixVertexUnfolding.Geometry.GeodesicCurveNonbranching

/-! At an interior-face target, distinct actual routes have distinct terminal
sources. Thus active sources count routes exactly. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Two geodesics with the same endpoints and terminal source are the same route. -/
theorem routes_agree_of_terminal_source (f g : P.BoundaryCurve)
    (hf : f ∈ P.geodesicCurves) (hg : g ∈ P.geodesicCurves) (different : f 0 ≠ f 1)
    (first : f 0 = g 0) (last : f 1 = g 1) (F : P.Face) (source : Plane)
    (left : P.HasTerminalSource f F source) (right : P.HasTerminalSource g F source) : f = g := by
  obtain ⟨s, s_before, left⟩ := left
  obtain ⟨u, u_before, right⟩ := right
  obtain ⟨t, after, before⟩ := exists_between (max_lt s_before u_before)
  have left_t := left t ⟨(le_max_left s u).trans after.le, before.le⟩
  have right_t := right t ⟨(le_max_right s u).trans after.le, before.le⟩
  have coordinates : P.faceCoordinates F (f t) = P.faceCoordinates F (g t) := by
    rw [left_t.2, right_t.2, last]
  have meet : f t = g t := by
    apply Subtype.ext
    apply dist_eq_zero.mp
    rw [← P.faceCoordinates_rigid F _ left_t.1 _ right_t.1, coordinates, dist_self]
  exact graph.geodesic_curves_agree_of_meeting small_faces f g hf hg different first last t
    ((unitInterval.nonneg s).trans_lt ((le_max_left s u).trans_lt after)) before meet

include graph small_faces in
/-- Active source copies are in bijection with actual normalized shortest routes. -/
theorem routes_equiv_active_sources (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    Nonempty (P.geodesicFiber a b ≃ P.activeSources a b F) := by
  classical
  have sources (f : P.geodesicFiber a b) : ∃ source, P.HasTerminalSource f.val F source := by
    have first : f.val 0 = a := congrArg Prod.fst f.property.2
    have last : f.val 1 = b := congrArg Prod.snd f.property.2
    obtain ⟨source, _, terminal⟩ := graph.exists_terminal_source small_faces f.val f.property.1
      (by simpa only [first, last] using different) F (by simpa only [last] using unique_face)
    exact ⟨source, terminal⟩
  choose source terminal using sources
  let code (f : P.geodesicFiber a b) : P.activeSources a b F := ⟨source f, f.val, f.property, terminal f⟩
  have injective : Function.Injective code := by
    intro f g equal
    apply Subtype.ext
    have first : f.val 0 = a := congrArg Prod.fst f.property.2
    have last : f.val 1 = b := congrArg Prod.snd f.property.2
    apply graph.routes_agree_of_terminal_source small_faces f.val g.val f.property.1 g.property.1
      (by simpa only [first, last] using different)
      ((congrArg Prod.fst f.property.2).trans (congrArg Prod.fst g.property.2).symm)
      ((congrArg Prod.snd f.property.2).trans (congrArg Prod.snd g.property.2).symm) F (source f) (terminal f)
    have same : source f = source g := congrArg Subtype.val equal
    rw [same]
    exact terminal g
  have surjective : Function.Surjective code := by
    intro q
    obtain ⟨f, hf, actual⟩ := q.property
    refine ⟨⟨f, hf⟩, Subtype.ext ?_⟩
    exact (terminal ⟨f, hf⟩).unique actual
  exact ⟨Equiv.ofBijective code ⟨injective, surjective⟩⟩

include graph small_faces in
/-- The finite active-source set has exactly as many elements as the route fiber. -/
theorem activeSources_ncard (a b : frontier P.body) (different : a ≠ b)
    (F : P.Face) (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F) :
    (P.activeSources a b F).ncard = Nat.card (P.geodesicFiber a b) := by
  obtain ⟨equiv⟩ := graph.routes_equiv_active_sources small_faces a b different F unique_face
  exact (Nat.card_congr equiv).symm

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
