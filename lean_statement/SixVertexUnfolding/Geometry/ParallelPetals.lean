import SixVertexUnfolding.Geometry.DomeDevelopment
import SixVertexUnfolding.Geometry.PlaneOrientation

/-! Petals unfolded outward from distinct parallel base hinges have disjoint closed images. -/

namespace SixVertexUnfolding

/-- The two exterior halfplanes of parallel supporting hinges do not meet. -/
theorem parallel_outward_sets_disjoint (a b c d : Plane) (left right : Set Plane)
    (ab : a ≠ b) (cd : c ≠ d) (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Plane))
    (r : ℝ) (parallel : d - c = r • (b - a))
    (left_outward : ∀ x ∈ left, OppositeHingeSides a b c x)
    (right_outward : ∀ x ∈ right, OppositeHingeSides c d a x) : Disjoint left right := by
  have r_ne : r ≠ 0 := by
    intro zero
    rw [zero, zero_smul] at parallel
    exact cd (sub_eq_zero.mp parallel).symm
  have area_ne := det_ne_zero_of_noncollinear a b c noncollinear
  apply Set.disjoint_left.mpr
  intro x hx hy
  have first := (oppositeHingeSides_iff_det a b c x ab).mp (left_outward x hx)
  have second := (oppositeHingeSides_iff_det c d a x cd).mp (right_outward x hy)
  have reverse : a - c = -(c - a) := by module
  have shifted : x - c = (x - a) - (c - a) := by module
  rw [parallel, det_smul_left, det_smul_left, reverse, det_neg_right,
    shifted, det_sub_right (b - a) (x - a) (c - a)] at second
  have scaled := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) first
  have gap := mul_pos (sq_pos_of_ne_zero r_ne) (sq_pos_of_ne_zero area_ne)
  nlinarith

namespace ConvexPolyhedron.Dome.Development

variable {P : ConvexPolyhedron} {dome : P.Dome} (net : dome.Development)

/-- The parallel-hinge branch is proved for the actual whole-facet dome development. -/
theorem parallel_petals_disjoint (F G : P.Face) (F_side : F ≠ dome.base) (G_side : G ≠ dome.base)
    (a b c d : P.Vertex) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (cd : c ≠ d)
    (aB : (a : Space) ∈ dome.base.val) (bB : (b : Space) ∈ dome.base.val)
    (cB : (c : Space) ∈ dome.base.val) (dB : (d : Space) ∈ dome.base.val)
    (aF : (a : Space) ∈ F.val) (bF : (b : Space) ∈ F.val)
    (cG : (c : Space) ∈ G.val) (dG : (d : Space) ∈ G.val)
    (r : ℝ) (parallel : (d : Space) - c = r • ((b : Space) - a)) :
    Disjoint (net.place F '' F.val) (net.place G '' G.val) := by
  let base := net.place dome.base
  have different (x y : P.Vertex) (hx : (x : Space) ∈ dome.base.val)
      (hy : (y : Space) ∈ dome.base.val) (ne : x ≠ y) : base x ≠ base y := by
    intro same
    have distance := net.rigid dome.base x hx y hy
    change dist (base x) (base y) = dist (x : Space) y at distance
    have points : (x : Space) = y := dist_eq_zero.mp (by simpa [same] using distance.symm)
    exact ne (Subtype.ext points)
  have placed := P.placed_triangle_noncollinear a b c ab ac bc (base a) (base b) (base c)
    (net.rigid dome.base a aB b bB) (net.rigid dome.base a aB c cB) (net.rigid dome.base b bB c cB)
  have flat_parallel : base d - base c = r • (base b - base a) := by
    have mapped := congrArg base.linear parallel
    have map_difference (v w : Space) : base.linear (v - w) = base v - base w := base.linearMap_vsub v w
    simpa only [map_smul, map_difference] using mapped
  apply parallel_outward_sets_disjoint (base a) (base b) (base c) (base d) _ _
    (different a b aB bB ab) (different c d cB dB cd) placed r flat_parallel
  · rintro _ ⟨x, hx, rfl⟩
    exact net.outward F F_side a ⟨⟨aB, aF⟩, a.property⟩ b ⟨⟨bB, bF⟩, b.property⟩
      (fun same => ab (Subtype.ext same)) c cB x hx
  · rintro _ ⟨x, hx, rfl⟩
    exact net.outward G G_side c ⟨⟨cB, cG⟩, c.property⟩ d ⟨⟨dB, dG⟩, d.property⟩
      (fun same => cd (Subtype.ext same)) a aB x hx

end ConvexPolyhedron.Dome.Development
end SixVertexUnfolding
