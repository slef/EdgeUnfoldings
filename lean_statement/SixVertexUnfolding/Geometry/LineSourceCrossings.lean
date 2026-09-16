import SixVertexUnfolding.Geometry.SourceBisectors

/-! Along a straight line, two source distances either agree everywhere
or tie at at most one parameter. Thus finitely many sources give finitely
many exceptional parameters. -/

namespace SixVertexUnfolding

open Set

theorem affine_real_line_formula (line : ℝ →ᵃ[ℝ] Plane) (t : ℝ) :
    line t = t • line.linear 1 + line 0 := by
  have linear : line.linear t = t • line.linear 1 := by
    simpa only [smul_eq_mul, mul_one] using line.linear.map_smul t (1 : ℝ)
  exact (congrFun line.decomp t).trans (congrArg (fun x => x + line 0) linear)

/-- Two ties on a line force the two distance functions to agree everywhere on it. -/
theorem source_distances_agree_on_line (line : ℝ →ᵃ[ℝ] Plane) (p q : Plane)
    {s t : ℝ} (different : s ≠ t)
    (at_s : dist p (line s) = dist q (line s))
    (at_t : dist p (line t) = dist q (line t)) :
    ∀ r, dist p (line r) = dist q (line r) := by
  rw [equal_site_distances_iff_bisector, affine_real_line_formula, inner_add_right, inner_smul_right] at at_s at_t
  have slope : inner ℝ (q - p) (line.linear 1) = 0 := by
    have product : (s - t) * inner ℝ (q - p) (line.linear 1) = 0 := by linarith
    exact (mul_eq_zero.mp product).resolve_left (sub_ne_zero.mpr different)
  intro r
  rw [equal_site_distances_iff_bisector, affine_real_line_formula, inner_add_right, inner_smul_right, slope, mul_zero, zero_add]
  simpa only [slope, mul_zero, zero_add] using at_s

/-- Parameters where two candidate source distances tie without agreeing along the entire line. -/
def lineSourceCrossings (sources : Set Plane) (line : ℝ →ᵃ[ℝ] Plane) : Set ℝ :=
  {t | ∃ p ∈ sources, ∃ q ∈ sources, dist p (line t) = dist q (line t) ∧
    ¬ ∀ s, dist p (line s) = dist q (line s)}

theorem lineSourceCrossings_finite (sources : Set Plane) (finite : sources.Finite)
    (line : ℝ →ᵃ[ℝ] Plane) : (lineSourceCrossings sources line).Finite := by
  letI : Fintype sources := finite.fintype
  let crossings (p q : sources) : Set ℝ :=
    {t | dist p.val (line t) = dist q.val (line t) ∧
      ¬ ∀ s, dist p.val (line s) = dist q.val (line s)}
  have each (p q : sources) : (crossings p q).Finite := by
    apply Set.Subsingleton.finite
    intro s hs t ht
    by_contra different
    exact hs.2 (source_distances_agree_on_line line p q different hs.1 ht.1)
  apply (finite_iUnion (fun p => finite_iUnion (each p))).subset
  rintro t ⟨p, hp, q, hq, equal, varying⟩
  exact mem_iUnion.mpr ⟨⟨p, hp⟩, mem_iUnion.mpr ⟨⟨q, hq⟩, equal, varying⟩⟩

/-- Away from the finite crossings, any pair tied at one parameter stays tied along the line. -/
theorem source_tie_persists_on_line (sources : Set Plane) (line : ℝ →ᵃ[ℝ] Plane) {t : ℝ}
    (regular : t ∉ lineSourceCrossings sources line) {p q : Plane}
    (hp : p ∈ sources) (hq : q ∈ sources) (tie : dist p (line t) = dist q (line t)) :
    ∀ s, dist p (line s) = dist q (line s) := by
  by_contra varying
  exact regular ⟨p, hp, q, hq, tie, varying⟩

end SixVertexUnfolding
