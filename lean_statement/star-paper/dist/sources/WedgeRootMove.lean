import SixVertexUnfolding.Geometry.PlanarDirections
import SixVertexUnfolding.Geometry.TriangleEdgeHalfplanes

/-! The root-moving step in Kiazyk's wedge argument, in Cartesian coordinates.

The two source images are `(0,h)` and `(0,-h)`. The root is `(r,0)`.
The upper outer ray has direction `(a,b)` and the lower one is its reflection.
The chosen region is to the left of the two inner legs. The definition covers
diverging rays, a bounded wedge, and the complement of a bounded wedge.
No boundedness or convexity of the wedge is assumed.
-/

namespace SixVertexUnfolding.Wedge

open Set

/-- The region bounded by the two inner segments and the two outer rays. -/
def region (h r a b : ℝ) : Set Plane := {z |
  (h ≤ |z 1| ∧ (if 0 < b then b * z 0 ≤ a * (|z 1| - h) else 0 < a)) ∨
  (|z 1| ≤ h ∧
    (if 0 ≤ b then h * z 0 ≤ r * (h - |z 1|)
     else if a < 0 then
       h * z 0 ≤ r * (h - |z 1|) ∧ b * z 0 ≤ a * (|z 1| - h)
     else h * z 0 ≤ r * (h - |z 1|) ∨ b * z 0 ≤ a * (|z 1| - h)))}

/-- Horizontal sections of the kite with base `(r,0)--(q,0)` and apices `(0,±h)`. -/
def kite (h r q : ℝ) : Set Plane := {z |
  |z 1| ≤ h ∧ r * (h - |z 1|) ≤ h * z 0 ∧
    h * z 0 ≤ q * (h - |z 1|)}

/-- The strict inequalities describing the inside of that kite. -/
def openKite (h r q : ℝ) : Set Plane := {z |
  |z 1| < h ∧ r * (h - |z 1|) < h * z 0 ∧
    h * z 0 < q * (h - |z 1|)}

/-- Ordinary Cartesian coordinates in the public Euclidean plane. -/
def point (x y : ℝ) : Plane := !₂[x, y]

private theorem upper_triangle {h r q : ℝ} (hp : 0 < h) (rq : r < q) (z : Plane) :
    z ∈ convexHull ℝ ({point r 0, point q 0, point 0 h} : Set Plane) ↔
      0 ≤ z 1 ∧ r * (h - z 1) ≤ h * z 0 ∧ h * z 0 ≤ q * (h - z 1) := by
  have area : 0 < det (point q 0 - point r 0) (point 0 h - point r 0) := by
    simpa [point, det, PiLp.sub_apply] using mul_pos (sub_pos.mpr rq) hp
  rw [triangle_mem_iff_edge_sides _ _ _ _ area]
  simp only [point, det, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, sub_zero, zero_sub, zero_mul]
  constructor
  · rintro ⟨base, right, left⟩
    exact ⟨(mul_nonneg_iff_of_pos_left (sub_pos.mpr rq)).mp base, by nlinarith, by nlinarith⟩
  · rintro ⟨base, left, right⟩
    exact ⟨mul_nonneg (sub_pos.mpr rq).le base, by nlinarith, by nlinarith⟩

private theorem lower_triangle {h r q : ℝ} (hp : 0 < h) (rq : r < q) (z : Plane) :
    z ∈ convexHull ℝ ({point q 0, point r 0, point 0 (-h)} : Set Plane) ↔
      z 1 ≤ 0 ∧ r * (h + z 1) ≤ h * z 0 ∧ h * z 0 ≤ q * (h + z 1) := by
  have area : 0 < det (point r 0 - point q 0) (point 0 (-h) - point q 0) := by
    have positive := mul_pos (sub_pos.mpr rq) hp
    simp [point, det, PiLp.sub_apply]
    nlinarith
  rw [triangle_mem_iff_edge_sides _ _ _ _ area]
  simp only [point, det, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, sub_zero, zero_sub, zero_mul]
  constructor
  · rintro ⟨base, left, right⟩
    have nonpos : z 1 ≤ 0 := by
      by_contra hz
      have := mul_neg_of_neg_of_pos (sub_neg.mpr rq) (lt_of_not_ge hz)
      linarith
    exact ⟨nonpos, by nlinarith, by nlinarith⟩
  · rintro ⟨base, left, right⟩
    exact ⟨mul_nonneg_of_nonpos_of_nonpos (sub_neg.mpr rq).le base, by nlinarith, by nlinarith⟩

/-- The coordinate kite is exactly the union of the two actual closed triangles. -/
theorem kite_eq_triangles {h r q : ℝ} (hp : 0 < h) (rq : r < q) :
    kite h r q =
      convexHull ℝ ({point r 0, point q 0, point 0 h} : Set Plane) ∪
      convexHull ℝ ({point q 0, point r 0, point 0 (-h)} : Set Plane) := by
  ext z
  rw [mem_union, upper_triangle hp rq, lower_triangle hp rq]
  change (|z 1| ≤ h ∧ r * (h - |z 1|) ≤ h * z 0 ∧
    h * z 0 ≤ q * (h - |z 1|)) ↔ _
  constructor
  · rintro ⟨_, lower, upper⟩
    by_cases positive : 0 ≤ z 1
    · exact Or.inl ⟨positive, by simpa [abs_of_nonneg positive] using lower,
        by simpa [abs_of_nonneg positive] using upper⟩
    · exact Or.inr ⟨(lt_of_not_ge positive).le,
        by simpa [abs_of_neg (lt_of_not_ge positive)] using lower,
        by simpa [abs_of_neg (lt_of_not_ge positive)] using upper⟩
  · rintro (⟨positive, lower, upper⟩ | ⟨negative, lower, upper⟩)
    · rw [abs_of_nonneg positive]
      refine ⟨?_, lower, upper⟩
      have product : 0 ≤ (q - r) * (h - z 1) := by nlinarith
      have := (mul_nonneg_iff_of_pos_left (sub_pos.mpr rq)).mp product
      linarith
    · rw [abs_of_nonpos negative]
      simp only [sub_neg_eq_add]
      refine ⟨?_, lower, upper⟩
      have product : 0 ≤ (q - r) * (h + z 1) := by nlinarith
      have := (mul_nonneg_iff_of_pos_left (sub_pos.mpr rq)).mp product
      linarith

/-- These strict inequalities describe the ordinary planar interior, including
points on the shared base of the two triangles. -/
theorem interior_kite {h r q : ℝ} (hp : 0 < h) :
    interior (kite h r q) = openKite h r q := by
  have cx : Continuous (fun z : Plane => z 0) := (EuclideanSpace.proj 0).continuous
  have cy : Continuous (fun z : Plane => |z 1|) := (EuclideanSpace.proj 1).continuous.abs
  have opened : IsOpen (openKite h r q) :=
    (isOpen_lt cy continuous_const).inter
      ((isOpen_lt (continuous_const.mul (continuous_const.sub cy)) (continuous_const.mul cx)).inter
       (isOpen_lt (continuous_const.mul cx) (continuous_const.mul (continuous_const.sub cy))))
  apply Subset.antisymm
  · intro z member
    obtain ⟨ε, εpos, near⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp member)
    have halfpos : 0 < ε / 2 := half_pos εpos
    have shifted (t : ℝ) (ht : |t| < ε) : z + t • direction 0 ∈ kite h r q := by
      apply near
      change dist (z + t • direction 0) z < ε
      simpa [dist_eq_norm, norm_smul, direction_norm, Real.norm_eq_abs] using ht
    have minus := shifted (-(ε / 2)) (by rw [abs_neg, abs_of_pos halfpos]; linarith)
    have plus := shifted (ε / 2) (by rw [abs_of_pos halfpos]; linarith)
    change _ ∧ _ ∧ _ at minus plus
    simp only [PiLp.add_apply, PiLp.smul_apply, direction_x, direction_y, Real.cos_zero,
      Real.sin_zero, smul_eq_mul, mul_one, mul_zero, add_zero] at minus plus
    have lower : r * (h - |z 1|) < h * z 0 := by nlinarith [mul_pos hp halfpos]
    have upper : h * z 0 < q * (h - |z 1|) := by nlinarith [mul_pos hp halfpos]
    refine ⟨?_, lower, upper⟩
    have height := minus.1
    apply lt_of_le_of_ne height
    intro boundary
    rw [boundary, sub_self, mul_zero] at lower upper
    linarith
  · intro z member
    exact mem_interior.mpr ⟨openKite h r q,
      fun _ hmem => ⟨hmem.1.le, hmem.2.1.le, hmem.2.2.le⟩, opened, member⟩

/-- The paper's range `π/2 ≤ γ ≤ 3π/2` gives exactly the outward condition.
The ray is obtained by rotating the vector from the upper apex to the root
clockwise by `γ`. -/
theorem outward_of_angle_range (h r γ : ℝ)
    (lower : Real.pi / 2 ≤ γ) (upper : γ ≤ 3 * Real.pi / 2) :
    0 ≤ h * (-r * Real.sin γ - h * Real.cos γ) -
      r * (r * Real.cos γ - h * Real.sin γ) := by
  have cosine := Real.cos_nonpos_of_pi_div_two_le_of_le lower (by linarith : γ ≤ Real.pi + Real.pi / 2)
  have product := mul_nonpos_of_nonneg_of_nonpos (add_nonneg (sq_nonneg r) (sq_nonneg h)) cosine
  nlinarith

/-- Moving the inner root to the right expands the region, with fixed outer rays. -/
theorem region_mono {h r q a b : ℝ} (order : r ≤ q) :
    region h r a b ⊆ region h q a b := by
  rintro z (outside | ⟨height, inside⟩)
  · exact Or.inl outside
  · refine Or.inr ⟨height, ?_⟩
    have bound := mul_le_mul_of_nonneg_right order (sub_nonneg.mpr height)
    dsimp only at inside ⊢
    split_ifs at inside ⊢ with up left
    · exact inside.trans bound
    · exact ⟨inside.1.trans bound, inside.2⟩
    · exact inside.imp (fun hx => hx.trans bound) id

/-- Every point gained by moving the root belongs to the intervening kite. -/
theorem region_subset_union_kite {h r q a b : ℝ} :
    region h q a b ⊆ region h r a b ∪ kite h r q := by
  rintro z (outside | ⟨height, inside⟩)
  · exact Or.inl (Or.inl outside)
  · by_cases before : h * z 0 ≤ r * (h - |z 1|)
    · apply Or.inl
      refine Or.inr ⟨height, ?_⟩
      dsimp only at inside ⊢
      split_ifs at inside ⊢ with up left
      · exact before
      · exact ⟨before, inside.2⟩
      · exact Or.inl before
    · dsimp only at inside
      split_ifs at inside with up left
      · exact Or.inr ⟨height, (lt_of_not_ge before).le, inside⟩
      · exact Or.inr ⟨height, (lt_of_not_ge before).le, inside.1⟩
      · rcases inside with lower | outer
        · exact Or.inr ⟨height, (lt_of_not_ge before).le, lower⟩
        · exact Or.inl (Or.inr ⟨height, by simp [up, left, outer]⟩)

/-- The nonnegative dot product says the outer ray points away from the old root. -/
theorem kite_subset_region {h r q a b : ℝ} (height_pos : 0 < h)
    (outward : 0 ≤ h * b - r * a) : kite h r q ⊆ region h q a b := by
  rintro z ⟨height, lower, upper⟩
  refine Or.inr ⟨height, ?_⟩
  dsimp only
  split_ifs with up left
  · exact upper
  · refine ⟨upper, ?_⟩
    have bneg : b < 0 := lt_of_not_ge up
    have rpos : 0 < r := by
      have hb := mul_neg_of_pos_of_neg height_pos bneg
      by_contra hr
      have ra := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hr) left.le
      linarith
    have xnonneg : 0 ≤ z 0 := by
      have := mul_nonneg rpos.le (sub_nonneg.mpr height)
      nlinarith
    exact (mul_nonpos_of_nonpos_of_nonneg bneg.le xnonneg).trans
      (mul_nonneg_of_nonpos_of_nonpos left.le (sub_nonpos.mpr height))
  · exact Or.inl upper

/-- Root movement adds exactly the kite; it cannot sweep up any other region. -/
theorem move_root {h r q a b : ℝ} (height_pos : 0 < h) (order : r ≤ q)
    (outward : 0 ≤ h * b - r * a) :
    region h q a b = region h r a b ∪ kite h r q := by
  apply Subset.antisymm region_subset_union_kite
  exact union_subset (region_mono order) (kite_subset_region height_pos outward)

/-- Before the move, the next kite's inside is outside the wedge.
The second outward condition is the angle budget at the new root. -/
theorem next_kite_outside {h r q a b : ℝ} (height_pos : 0 < h)
    (outward : 0 ≤ h * b - q * a) :
    Disjoint (region h r a b) (openKite h r q) := by
  apply Set.disjoint_left.mpr
  rintro z (outside | ⟨height, inside⟩) ⟨strict_height, lower, upper⟩
  · exact (not_le_of_gt strict_height) outside.1
  · dsimp only at inside
    split_ifs at inside with up left
    · exact (not_le_of_gt lower) inside
    · exact (not_le_of_gt lower) inside.1
    · rcases inside with old | outer
      · exact (not_le_of_gt lower) old
      · have bneg : b < 0 := lt_of_not_ge up
        have apos : 0 < a := by
          have anonneg := le_of_not_gt left
          by_contra ha
          have azero : a = 0 := le_antisymm (le_of_not_gt ha) anonneg
          rw [azero, mul_zero, sub_zero] at outward
          exact (not_le_of_gt (mul_neg_of_pos_of_neg height_pos bneg)) outward
        have qneg : q < 0 := by
          have hb := mul_neg_of_pos_of_neg height_pos bneg
          by_contra hq
          have qa := mul_nonneg (le_of_not_gt hq) apos.le
          linarith
        have xneg : z 0 < 0 := by
          have := mul_neg_of_neg_of_pos qneg (sub_pos.mpr strict_height)
          nlinarith
        have positive := mul_pos_of_neg_of_neg bneg xneg
        have negative := mul_neg_of_pos_of_neg apos (sub_neg.mpr strict_height)
        linarith

/-- The root-moving and next-kite separation step, with ordinary planar interior. -/
theorem root_step {h r q a b : ℝ} (height_pos : 0 < h) (order : r ≤ q)
    (old_outward : 0 ≤ h * b - r * a) (new_outward : 0 ≤ h * b - q * a) :
    region h q a b = region h r a b ∪ kite h r q ∧
      Disjoint (region h r a b) (interior (kite h r q)) := by
  refine ⟨move_root height_pos order old_outward, ?_⟩
  rw [interior_kite height_pos]
  exact next_kite_outside height_pos new_outward

end SixVertexUnfolding.Wedge
