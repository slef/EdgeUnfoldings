import SixVertexUnfolding.Geometry.GeodesicFibers

/-! On endpoint pairs with a unique shortest route, choosing a shortest
route is automatically continuous in the uniform metric. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter
open scoped Topology

/-- Choose one normalized shortest route for each boundary endpoint pair. -/
noncomputable def chosenGeodesic (P : ConvexPolyhedron)
    (ends : (frontier P.body) × (frontier P.body)) : P.BoundaryCurve :=
  (P.geodesicFiber_nonempty ends.1 ends.2).choose

theorem chosenGeodesic_mem (P : ConvexPolyhedron) (ends : (frontier P.body) × (frontier P.body)) :
    P.chosenGeodesic ends ∈ P.geodesicFiber ends.1 ends.2 :=
  (P.geodesicFiber_nonempty ends.1 ends.2).choose_spec

/-- Uniform continuity at a unique route follows from compactness, without any six-vertex hypothesis. -/
theorem chosenGeodesic_continuousAt (P : ConvexPolyhedron)
    (ends : (frontier P.body) × (frontier P.body))
    (unique : (P.geodesicFiber ends.1 ends.2).Subsingleton) :
    ContinuousAt P.chosenGeodesic ends := by
  apply continuousAt_def.mpr
  intro U neighborhood
  obtain ⟨W, subset, openW, chosenW⟩ := mem_nhds_iff.mp neighborhood
  obtain ⟨V, openV, endsV, contains⟩ := P.geodesic_family_upper_continuous ends W openW
    (fun f geodesic endpoint => unique ⟨geodesic, endpoint⟩ (P.chosenGeodesic_mem ends) ▸ chosenW)
  apply Filter.mem_of_superset (openV.mem_nhds endsV)
  intro pair near
  apply subset
  exact contains (P.chosenGeodesic pair) (P.chosenGeodesic_mem pair).1
    ((P.chosenGeodesic_mem pair).2 ▸ near)

/-- The route-selection map is continuous on the complete unique-route locus. -/
theorem chosenGeodesic_continuousOn (P : ConvexPolyhedron) :
    ContinuousOn P.chosenGeodesic
      {ends : (frontier P.body) × (frontier P.body) | (P.geodesicFiber ends.1 ends.2).Subsingleton} :=
  fun ends unique => (P.chosenGeodesic_continuousAt ends unique).continuousWithinAt

end SixVertexUnfolding.ConvexPolyhedron
