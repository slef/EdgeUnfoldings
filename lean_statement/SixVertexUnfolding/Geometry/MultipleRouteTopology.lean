import SixVertexUnfolding.Geometry.UniqueGeodesicNeighborhoods
import SixVertexUnfolding.Geometry.MultipleShortestRoutes
import SixVertexUnfolding.Geometry.UniqueTargetContraction

/-! The original multiple-route locus agrees with nonsingleton geodesic
fibers. It is relatively closed in the source-deleted interior of each face. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- The compact-family formulation detects exactly the original notion of multiple shortest routes. -/
theorem multiple_routes_iff_fiber (P : ConvexPolyhedron) (a b : frontier P.body) :
    (b : Space) ∈ P.multipleRouteLocus a ↔ a ≠ b ∧ ¬ (P.geodesicFiber a b).Subsingleton := by
  constructor
  · rintro ⟨different, first, second, hs, ht, fs, ft, cs, ct, distinct⟩
    refine ⟨fun h => different (congrArg Subtype.val h), ?_⟩
    intro unique
    have first_ends : P.curveEndpoints first.boundaryCurve = (a, b) := by
      apply Prod.ext <;> apply Subtype.ext
      · exact first.curve.source
      · exact first.curve.target
    have second_ends : P.curveEndpoints second.boundaryCurve = (a, b) := by
      apply Prod.ext <;> apply Subtype.ext
      · exact second.curve.source
      · exact second.curve.target
    have same := unique ⟨first.boundaryCurve_geodesic hs fs cs, first_ends⟩
      ⟨second.boundaryCurve_geodesic ht ft ct, second_ends⟩
    apply distinct
    intro t
    exact congrArg (fun f : P.BoundaryCurve => (f t : Space)) same
  · rintro ⟨different, multiple⟩
    have witnesses : ∃ f ∈ P.geodesicFiber a b, ∃ g ∈ P.geodesicFiber a b, f ≠ g := by
      by_contra none
      apply multiple
      intro f hf g hg
      by_contra unequal
      exact none ⟨f, hf, g, hg, unequal⟩
    obtain ⟨f, hf, g, hg, unequal⟩ := witnesses
    obtain ⟨first, hs, fs, cs, first_eq⟩ := P.geodesicFiber_path a b f hf
    obtain ⟨second, ht, ft, ct, second_eq⟩ := P.geodesicFiber_path a b g hg
    refine ⟨fun h => different (Subtype.ext h), first, second, hs, ht, fs, ft, cs, ct, ?_⟩
    intro same
    apply unequal
    rw [← first_eq, ← second_eq, first.eq_of_curve_eq second same]

/-- The unique-route target set is exactly the complement of the original multiple-route locus. -/
theorem uniqueTargets_eq_complement_multiple (P : ConvexPolyhedron) (a : frontier P.body) :
    P.uniqueTargets a = {b : frontier P.body | (b : Space) ∉ P.multipleRouteLocus a} := by
  ext b
  change (P.geodesicFiber a b).Subsingleton ↔ (b : Space) ∉ P.multipleRouteLocus a
  rw [P.multiple_routes_iff_fiber a b]
  by_cases same : a = b
  · subst b
    simp [P.geodesicFiber_self a]
  · constructor
    · intro unique multiple
      exact multiple.2 unique
    · intro absent
      by_contra multiple
      exact absent ⟨same, multiple⟩

/-- Removing precisely the multiple-route targets leaves a contractible subset of the actual boundary. -/
theorem multiple_route_complement_contractible (P : ConvexPolyhedron) (a : frontier P.body) :
    ContractibleSpace {b : frontier P.body | (b : Space) ∉ P.multipleRouteLocus a} := by
  rw [← P.uniqueTargets_eq_complement_multiple a]
  exact P.uniqueTargets_contractible a

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- A limit of multiple-route targets is still a multiple-route target if it stays away from the source and face edges. -/
theorem multiple_routes_closed_within_face (a : frontier P.body) (F : P.Face)
    (b : frontier P.body) (different : a ≠ b)
    (unique_face : ∀ G : P.Face, (b : Space) ∈ G.val → G = F)
    (limit : b ∈ closure {c : frontier P.body | (c : Space) ∈ P.multipleRouteLocus a}) :
    (b : Space) ∈ P.multipleRouteLocus a := by
  rw [P.multiple_routes_iff_fiber a b]
  refine ⟨different, ?_⟩
  intro unique_route
  obtain ⟨V, openV, bV, unique_near⟩ := graph.unique_geodesics_nearby small_faces
    a b different F unique_face unique_route
  obtain ⟨c, cV, multiple⟩ := mem_closure_iff.mp limit V openV bV
  exact ((P.multiple_routes_iff_fiber a c).mp multiple).2 (unique_near c cV)

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
