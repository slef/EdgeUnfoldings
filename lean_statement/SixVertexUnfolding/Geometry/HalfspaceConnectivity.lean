import SixVertexUnfolding.Geometry.EdgeConnectivity
import SixVertexUnfolding.Geometry.HeightPerturbation

/-! Vertices strictly on one side of any plane induce a connected graph when nonempty. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Ascending edges stay inside any set closed under strict increases of the chosen height. -/
theorem reachable_to_maximum_in_upper_set (P : ConvexPolyhedron) (height : Space)
    (s : Set P.Vertex) (top start : s)
    (strict : ∀ w : P.Vertex, w ≠ top.val → inner ℝ height w < inner ℝ height top.val)
    (upward : ∀ a ∈ s, ∀ b : P.Vertex, inner ℝ height a < inner ℝ height b → b ∈ s) :
    (P.edgeGraph.induce s).Reachable start top := by
  classical
  letI : Fintype s := Fintype.ofFinite _
  let graph := P.edgeGraph.induce s
  let component := Finset.univ.filter (fun w : s => graph.Reachable start w)
  have start_in : start ∈ component :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.rfl⟩
  obtain ⟨highest, highest_in, maximal⟩ := component.exists_max_image
    (fun w : s => inner ℝ height w.val) ⟨start, start_in⟩
  have reached : graph.Reachable start highest := (Finset.mem_filter.mp highest_in).2
  by_cases same : highest = top
  · exact same ▸ reached
  have lower := strict highest.val (fun equal => same (Subtype.ext equal))
  obtain ⟨next, adjacent, higher⟩ := P.exists_ascending_neighbor height highest.val ⟨top.val, lower⟩
  let next_in_s : s := ⟨next, upward highest.val highest.property next higher⟩
  have edge : graph.Adj highest next_in_s := adjacent
  have next_in : next_in_s ∈ component :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, reached.trans edge.reachable⟩
  exact False.elim (higher.not_ge (maximal next_in_s next_in))

/-- All original vertices strictly above a plane are joined by paths strictly above that plane. -/
theorem strict_halfspace_preconnected (P : ConvexPolyhedron) (height : Space) (level : ℝ) :
    (P.edgeGraph.induce {v : P.Vertex | level < inner ℝ height v}).Preconnected := by
  let s : Set P.Vertex := {v | level < inner ℝ height v}
  obtain ⟨m, top, strict, preserves⟩ := P.exists_height_with_unique_maximum height
  have upward : ∀ a ∈ s, ∀ b : P.Vertex, inner ℝ m a < inner ℝ m b → b ∈ s := by
    intro a ha b increasing
    by_contra below
    have reverse : inner ℝ height b < inner ℝ height a := (not_lt.mp below).trans_lt ha
    exact increasing.asymm (preserves b a reverse)
  intro start finish
  have top_in : top ∈ s := by
    by_cases same : start.val = top
    · exact same ▸ start.property
    · exact upward start.val start.property top (strict start.val same)
  let top_in_s : s := ⟨top, top_in⟩
  have reach (a : s) : (P.edgeGraph.induce s).Reachable a top_in_s :=
    P.reachable_to_maximum_in_upper_set m s top_in_s a strict upward
  exact (reach start).trans (reach finish).symm

/-- Halfspace paths avoid any deleted vertices on or below the bounding plane. -/
theorem halfspace_reachable_avoiding (P : ConvexPolyhedron) (height : Space) (level : ℝ)
    (deleted : Finset P.Vertex)
    (below : ∀ w ∈ deleted, inner ℝ height w ≤ level)
    (a b : {v : P.Vertex | v ∉ deleted})
    (a_above : level < inner ℝ height a.val) (b_above : level < inner ℝ height b.val) :
    (P.edgeGraph.induce {v : P.Vertex | v ∉ deleted}).Reachable a b := by
  have inclusion : {v : P.Vertex | level < inner ℝ height v} ⊆ {v | v ∉ deleted} := by
    intro w above removed
    exact above.not_ge (below w removed)
  have path := P.strict_halfspace_preconnected height level ⟨a.val, a_above⟩ ⟨b.val, b_above⟩
  exact path.map (SimpleGraph.induceHomOfLE _ inclusion).toHom

end SixVertexUnfolding.ConvexPolyhedron
