import SixVertexUnfolding.Geometry.VoronoiDiagram
import Mathlib.Geometry.Euclidean.Basic

/-! Three distinct sites can have only one common equidistant planar center.
Consequently a finite site list has only finitely many possible junctions. -/

namespace SixVertexUnfolding

open Set

/-- Two centers equidistant from three distinct planar sites must coincide. -/
theorem three_site_center_unique (p q r x y : Plane) (pq : p ≠ q) (pr : p ≠ r) (qr : q ≠ r)
    (xq : dist p x = dist q x) (xr : dist p x = dist r x)
    (yq : dist p y = dist q y) (yr : dist p y = dist r y) : x = y := by
  by_contra different
  have dimension : Module.finrank ℝ Plane = 2 := by simp [Plane]
  have alternatives := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two dimension
    different pq (rfl : dist p x = dist p x) xq.symm xr.symm
    (rfl : dist p y = dist p y) yq.symm yr.symm
  exact alternatives.elim (fun h => pr h.symm) (fun h => qr h.symm)

/-- A finite list has only finitely many points equidistant from three distinct sites. -/
theorem finite_three_site_centers (sources : Set Plane) (finite : sources.Finite) :
    {x : Plane | ∃ p ∈ sources, ∃ q ∈ sources, ∃ r ∈ sources,
      p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ dist p x = dist q x ∧ dist p x = dist r x}.Finite := by
  let centers (t : Plane × Plane × Plane) : Set Plane :=
    {x | t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
      dist t.1 x = dist t.2.1 x ∧ dist t.1 x = dist t.2.2 x}
  have one (t : Plane × Plane × Plane) : (centers t).Subsingleton := by
    intro x hx y hy
    exact three_site_center_unique t.1 t.2.1 t.2.2 x y hx.1 hx.2.1 hx.2.2.1
      hx.2.2.2.1 hx.2.2.2.2 hy.2.2.2.1 hy.2.2.2.2
  have all := (finite.prod (finite.prod finite)).biUnion (fun t _ => (one t).finite)
  apply all.subset
  rintro x ⟨p, hp, q, hq, r, hr, pq, pr, qr, xq, xr⟩
  exact mem_iUnion.mpr ⟨(p, q, r), mem_iUnion.mpr ⟨⟨hp, hq, hr⟩, pq, pr, qr, xq, xr⟩⟩

/-- With exactly two sites, every point of their bisector is a nearest-site tie. -/
theorem voronoiBoundary_pair (p q : Plane) (different : p ≠ q) :
    voronoiBoundary {p, q} = {x : Plane | dist p x = dist q x} := by
  ext x
  constructor
  · rintro ⟨r, hr, s, hs, distinct, tied, _⟩
    have r_cases : r = p ∨ r = q := by simpa only [mem_insert_iff, mem_singleton_iff] using hr
    have s_cases : s = p ∨ s = q := by simpa only [mem_insert_iff, mem_singleton_iff] using hs
    rcases r_cases with hr | hr <;> rcases s_cases with hs | hs
    · exact (distinct (hr.trans hs.symm)).elim
    · simpa only [hr, hs] using tied
    · simpa only [hr, hs] using tied.symm
    · exact (distinct (hr.trans hs.symm)).elim
  · intro tied
    refine ⟨p, by simp, q, by simp, different, tied, ?_⟩
    intro r hr
    rcases mem_insert_iff.mp hr with rfl | hr
    · exact le_rfl
    · simpa only [mem_singleton_iff.mp hr] using tied.le

end SixVertexUnfolding
