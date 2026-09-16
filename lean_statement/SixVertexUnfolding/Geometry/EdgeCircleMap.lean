import SixVertexUnfolding.Geometry.EmbeddedGraphGluing
import SixVertexUnfolding.Geometry.SegmentRealCoordinate

/-! Send one oriented graph edge once around the circle and every other
edge to zero. Endpoint values agree, so this is continuous on the exact trace. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} (K : P.EmbeddedCutGraph a)
  (u v : K.vertices)

/-- The selected open edge makes one turn; everything else maps to the base point. -/
noncomputable def edgeCircleMap (x : Space) : AddCircle (1 : ℝ) := by
  classical
  exact if x ∈ openSegment ℝ (u : Space) (v : Space) then
    (segmentCoordinate u v x : AddCircle (1 : ℝ)) else 0

theorem edgeCircleMap_on_vertex (edge : K.graph.Adj u v) (w : K.vertices) : K.edgeCircleMap u v w = 0 := by
  classical
  apply if_neg
  exact fun member => disjoint_left.mp (K.no_vertex_inside u v edge) member w.property

theorem edgeCircleMap_on_selected (edge : K.graph.Adj u v) {x : Space}
    (hx : x ∈ segment ℝ (u : Space) (v : Space)) :
    K.edgeCircleMap u v x = (segmentCoordinate u v x : AddCircle (1 : ℝ)) := by
  classical
  have different : (u : Space) ≠ (v : Space) := fun same => edge.ne (Subtype.ext same)
  by_cases left : x = u
  · subst x
    rw [K.edgeCircleMap_on_vertex u v edge u, segmentCoordinate_left u v different, AddCircle.coe_zero]
  by_cases right : x = v
  · subst x
    rw [K.edgeCircleMap_on_vertex u v edge v, segmentCoordinate_right u v different, AddCircle.coe_period]
  exact if_pos (mem_openSegment_of_ne_left_right (Ne.symm left) (Ne.symm right) hx)

theorem edgeCircleMap_on_other (edge : K.graph.Adj u v) {p q : K.vertices}
    (other : K.graph.Adj p q) (different : ¬ ((u = p ∧ v = q) ∨ (u = q ∧ v = p)))
    {x : Space} (hx : x ∈ segment ℝ (p : Space) (q : Space)) : K.edgeCircleMap u v x = 0 := by
  classical
  apply if_neg
  intro selected
  have not_vertex : x ∉ K.vertices := fun vertex => disjoint_left.mp (K.no_vertex_inside u v edge) selected vertex
  have interior : x ∈ openSegment ℝ (p : Space) (q : Space) :=
    mem_openSegment_of_ne_left_right (fun equal => not_vertex (equal ▸ p.property))
      (fun equal => not_vertex (equal ▸ q.property)) hx
  exact different (K.open_edges_meet u v p q edge other x selected interior)

/-- The circle-valued function is continuous across all graph vertices and junctions. -/
theorem edgeCircleMap_continuous (edge : K.graph.Adj u v) :
    ContinuousOn (K.edgeCircleMap u v) (P.cutSetInSpace a) := by
  apply K.continuous_on_trace_of_edges
  intro p q other
  have selected_continuous : ContinuousOn (K.edgeCircleMap u v) (segment ℝ (u : Space) (v : Space)) := by
    apply ((AddCircle.isCoveringMap_coe (1 : ℝ)).continuous.comp
      (segmentCoordinate_continuous u v)).continuousOn.congr
    intro x hx
    exact K.edgeCircleMap_on_selected u v edge hx
  by_cases same : (u = p ∧ v = q) ∨ (u = q ∧ v = p)
  · rcases same with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact selected_continuous
    · rwa [segment_symm] at selected_continuous
  · apply continuousOn_const.congr
    intro x hx
    exact K.edgeCircleMap_on_other u v edge other same hx

end SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph
