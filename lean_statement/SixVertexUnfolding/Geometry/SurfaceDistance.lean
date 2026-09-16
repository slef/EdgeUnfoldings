import SixVertexUnfolding.Geometry.SurfacePathReversal

/-! Intrinsic distance on the actual boundary, defined from the existing
continuous surface paths. The distance is finite and attained. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set
open scoped ENNReal NNReal

/-- The infimum of lengths of continuous routes on the boundary. -/
noncomputable def surfaceEDist (P : ConvexPolyhedron) (a b : Space) : ℝ≥0∞ :=
  ⨅ path : P.SurfacePath a b, path.length

/-- Real-valued intrinsic distance; its metric properties are asserted on boundary points. -/
noncomputable def surfaceDist (P : ConvexPolyhedron) (a b : Space) : ℝ :=
  (P.surfaceEDist a b).toReal

/-- Every route bounds the intrinsic distance above. -/
theorem SurfacePath.surfaceEDist_le_length {P : ConvexPolyhedron} {a b : Space} (path : P.SurfacePath a b) :
    P.surfaceEDist a b ≤ path.length := iInf_le _ path

/-- Intrinsic distance is never smaller than the Euclidean chord. -/
theorem edist_le_surfaceEDist (P : ConvexPolyhedron) (a b : Space) :
    edist a b ≤ P.surfaceEDist a b := le_iInf fun path => path.chord_le_length

/-- Reversing routes makes intrinsic distance symmetric. -/
theorem surfaceEDist_comm (P : ConvexPolyhedron) (a b : Space) :
    P.surfaceEDist a b = P.surfaceEDist b a := by
  have bound (x y : Space) : P.surfaceEDist x y ≤ P.surfaceEDist y x := by
    apply le_iInf
    intro path
    exact path.reverse.surfaceEDist_le_length.trans_eq path.reverse_length
  exact le_antisymm (bound a b) (bound b a)

/-- A shortest route realizes the intrinsic distance. -/
theorem SurfacePath.length_eq_surfaceEDist {P : ConvexPolyhedron} {a b : Space}
    (path : P.SurfacePath a b) (shortest : path.IsShortest) : path.length = P.surfaceEDist a b :=
  le_antisymm (le_iInf shortest) path.surfaceEDist_le_length

/-- The shortest-path existence theorem shows that the infimum is attained and finite. -/
theorem exists_surface_distance_path (P : ConvexPolyhedron) {a b : Space}
    (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body) :
    ∃ path : P.SurfacePath a b, path.IsShortest ∧ path.length ≠ ⊤ ∧
      path.length = P.surfaceEDist a b := by
  obtain ⟨path, shortest, finite⟩ := P.exists_shortest_surface_path ha hb
  exact ⟨path, shortest, finite, le_antisymm (le_iInf shortest) path.surfaceEDist_le_length⟩

/-- Intrinsic distances between boundary points are finite. -/
theorem surfaceEDist_ne_top (P : ConvexPolyhedron) {a b : Space}
    (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body) : P.surfaceEDist a b ≠ ⊤ := by
  obtain ⟨path, _, finite, equal⟩ := P.exists_surface_distance_path ha hb
  exact equal ▸ finite

/-- Within any whole face the intrinsic distance is exactly the Euclidean distance. -/
theorem surfaceEDist_eq_edist_in_face (P : ConvexPolyhedron) (F : P.Face) {a b : Space}
    (ha : a ∈ F.val) (hb : b ∈ F.val) : P.surfaceEDist a b = edist a b := by
  exact le_antisymm
    ((SurfacePath.inFace F ha hb).surfaceEDist_le_length.trans_eq (SurfacePath.inFace_length F ha hb))
    (P.edist_le_surfaceEDist a b)

/-- A boundary point has zero intrinsic distance from itself. -/
theorem surfaceEDist_self (P : ConvexPolyhedron) {a : Space} (ha : a ∈ frontier P.body) :
    P.surfaceEDist a a = 0 := by
  obtain ⟨F, aF⟩ := P.boundary_point_in_face ha
  rw [P.surfaceEDist_eq_edist_in_face F aF aF, edist_self]

/-- Concatenating minimizing routes proves the intrinsic triangle inequality. -/
theorem surfaceEDist_triangle (P : ConvexPolyhedron) {a b c : Space}
    (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body) (hc : c ∈ frontier P.body) :
    P.surfaceEDist a c ≤ P.surfaceEDist a b + P.surfaceEDist b c := by
  obtain ⟨first, _, _, first_length⟩ := P.exists_surface_distance_path ha hb
  obtain ⟨second, _, _, second_length⟩ := P.exists_surface_distance_path hb hc
  have bound := (first.join second).surfaceEDist_le_length
  rwa [SurfacePath.join_length, first_length, second_length] at bound

/-- Real intrinsic distance is nonnegative. -/
theorem surfaceDist_nonneg (P : ConvexPolyhedron) (a b : Space) : 0 ≤ P.surfaceDist a b :=
  ENNReal.toReal_nonneg

theorem surfaceDist_comm (P : ConvexPolyhedron) (a b : Space) :
    P.surfaceDist a b = P.surfaceDist b a := by rw [surfaceDist, surfaceDist, P.surfaceEDist_comm]

theorem dist_le_surfaceDist (P : ConvexPolyhedron) {a b : Space}
    (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body) : dist a b ≤ P.surfaceDist a b := by
  simpa only [surfaceDist, edist_dist, ENNReal.toReal_ofReal dist_nonneg] using
    ENNReal.toReal_mono (P.surfaceEDist_ne_top ha hb) (P.edist_le_surfaceEDist a b)

theorem surfaceDist_eq_dist_in_face (P : ConvexPolyhedron) (F : P.Face) {a b : Space}
    (ha : a ∈ F.val) (hb : b ∈ F.val) : P.surfaceDist a b = dist a b := by
  rw [surfaceDist, P.surfaceEDist_eq_edist_in_face F ha hb, edist_dist, ENNReal.toReal_ofReal dist_nonneg]

theorem surfaceDist_self (P : ConvexPolyhedron) {a : Space} (ha : a ∈ frontier P.body) :
    P.surfaceDist a a = 0 := by rw [surfaceDist, P.surfaceEDist_self ha, ENNReal.toReal_zero]

theorem surfaceDist_triangle (P : ConvexPolyhedron) {a b c : Space}
    (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body) (hc : c ∈ frontier P.body) :
    P.surfaceDist a c ≤ P.surfaceDist a b + P.surfaceDist b c := by
  have bound := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨P.surfaceEDist_ne_top ha hb, P.surfaceEDist_ne_top hb hc⟩) (P.surfaceEDist_triangle ha hb hc)
  simpa only [surfaceDist, ENNReal.toReal_add (P.surfaceEDist_ne_top ha hb)
    (P.surfaceEDist_ne_top hb hc)] using bound

/-- Zero intrinsic distance identifies boundary points. -/
theorem surfaceDist_eq_zero_iff (P : ConvexPolyhedron) {a b : Space}
    (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body) : P.surfaceDist a b = 0 ↔ a = b := by
  constructor
  · intro zero
    exact dist_eq_zero.mp (le_antisymm ((P.dist_le_surfaceDist ha hb).trans_eq zero) dist_nonneg)
  · rintro rfl
    exact P.surfaceDist_self ha

end SixVertexUnfolding.ConvexPolyhedron
