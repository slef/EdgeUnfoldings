import SixVertexUnfolding.Geometry.GlobalTriangleMaps
import SixVertexUnfolding.Geometry.SourceNeighborhood

/-! For a source sharing a face with every original vertex, the star
cuts are simply the straight segments from the source to those vertices. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- The straight source-to-vertex cuts, viewed on the actual boundary. -/
def starCuts (P : ConvexPolyhedron) (a : frontier P.body) : Set (frontier P.body) :=
  {b | ∃ v : P.Vertex, (b : Space) ∈ segment ℝ (a : Space) (v : Space)}

/-- The actual boundary after removing those cut rays. -/
abbrev UncutSurface (P : ConvexPolyhedron) (a : frontier P.body) :=
  {b : frontier P.body // b ∉ P.starCuts a}

theorem source_mem_starCuts (P : ConvexPolyhedron) (a : frontier P.body) : a ∈ P.starCuts a := by
  obtain ⟨v, member⟩ := P.vertices_nonempty
  exact ⟨⟨v, member⟩, left_mem_segment ℝ _ _⟩

theorem starCuts_closed (P : ConvexPolyhedron) (a : frontier P.body) : IsClosed (P.starCuts a) := by
  have description : P.starCuts a = ⋃ v : P.Vertex,
      (fun b : frontier P.body => (b : Space)) ⁻¹' segment ℝ (a : Space) (v : Space) := by
    ext b
    simp only [starCuts, mem_setOf_eq, mem_iUnion, mem_preimage]
  rw [description]
  apply isClosed_iUnion_of_finite
  intro v
  have compact : IsCompact (segment ℝ (a : Space) (v : Space)) := by
    rw [segment_eq_image_lineMap]
    apply isCompact_Icc.image
    fun_prop
  exact compact.isClosed.preimage continuous_subtype_val

/-- Every shortest ray to an original cofacial vertex lies in the stated straight cut. -/
theorem original_route_subset_starCuts (P : ConvexPolyhedron) (a b : frontier P.body)
    (original : (b : Space) ∈ P.vertices) (F : P.Face) (source : (a : Space) ∈ F.val)
    (target : (b : Space) ∈ F.val) (route : P.BoundaryCurve) (member : route ∈ P.geodesicFiber a b) :
    range route ⊆ P.starCuts a := by
  obtain ⟨path, shortest, _, _, same⟩ := P.geodesicFiber_path a b route member
  rintro x ⟨t, rfl⟩
  refine ⟨⟨b, original⟩, ?_⟩
  have inside := path.shortest_cofacial_range_subset shortest F source target ⟨t, rfl⟩
  rw [← same]
  exact inside

namespace PlacedCutEdgeTriangles

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (D : PlacedCutEdgeTriangles T edge)

/-- A represented endpoint ray outside the star cuts cannot end at an original vertex. -/
theorem endpoint_nonvertex_of_outside_cuts
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {b : frontier P.body} {x : Plane} (outside : b ∉ P.starCuts a)
    (placed : D.PlacesOnRay 0 b x) : (u : Space) ∉ P.vertices := by
  intro original
  obtain ⟨F, source, target⟩ := cofacial ⟨u, original⟩
  obtain ⟨side, t, at_point, _⟩ := placed
  apply outside
  apply P.original_route_subset_starCuts a (T.vertexTarget u) original F source target (D.routes side 0)
  · simpa only [T.closedEdgeTarget_zero] using D.routes_member side 0
  · exact ⟨t, at_point⟩

end PlacedCutEdgeTriangles
end SixVertexUnfolding.ConvexPolyhedron
