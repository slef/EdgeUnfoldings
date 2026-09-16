import SixVertexUnfolding.Geometry.DomeVirtualCorner
import SixVertexUnfolding.Geometry.ParallelPetals

/-! Opposite dome petals are separated whether their extended base hinges meet or are parallel. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Dome.Development

variable {P : ConvexPolyhedron} {dome : P.Dome} (net : dome.Development)

/-- Two different base hinges, with one endpoint outside the other petal, give disjoint petal interiors. -/
theorem opposite_petals_nonoverlap {center : Space} (facets : P.NormalizedFacets center)
    (F G : P.Face) (F_side : F ≠ dome.base) (G_side : G ≠ dome.base)
    (a b c d : P.Vertex) (ab : a ≠ b) (cd : c ≠ d)
    (aB : (a : Space) ∈ dome.base.val) (bB : (b : Space) ∈ dome.base.val)
    (cB : (c : Space) ∈ dome.base.val) (dB : (d : Space) ∈ dome.base.val)
    (aF : (a : Space) ∈ F.val) (bF : (b : Space) ∈ F.val)
    (cG : (c : Space) ∈ G.val) (dG : (d : Space) ∈ G.val)
    (aG : (a : Space) ∉ G.val) (cF : (c : Space) ∉ F.val) :
    Disjoint (interior (net.place F '' F.val)) (interior (net.place G '' G.val)) := by
  have different : F ≠ G := fun same => aG (same ▸ aF)
  have ca : c ≠ a := fun same => aG (same ▸ cG)
  have da : d ≠ a := fun same => aG (same ▸ dG)
  by_cases parallel_height : inner ℝ (facets.normal G) ((b : Space) - a) = 0
  · have triangle := P.no_three_collinear_vertices c.property d.property a.property
      (fun same => cd (Subtype.ext same)) (fun same => ca (Subtype.ext same))
      (fun same => da (Subtype.ext same))
    obtain ⟨t, u, coordinates⟩ := dome.base.exists_triangle_coordinates c d a b cB dB aB bB triangle
    have axis := facets.difference_zero G (subset_affineSpan ℝ _ cG) (subset_affineSpan ℝ _ dG)
    have gap := facets.difference_negative G (subset_affineSpan ℝ _ cG)
      (P.vertices_subset_body a.property) aG
    have equal_height : inner ℝ (facets.normal G) ((b : Space) - c) =
        inner ℝ (facets.normal G) ((a : Space) - c) := by
      rw [inner_sub_right] at parallel_height ⊢
      rw [inner_sub_right]
      linarith
    have measured := congrArg (fun v : Space => inner ℝ (facets.normal G) v) coordinates
    simp only [inner_add_right, inner_smul_right, axis, mul_zero, zero_add, equal_height] at measured
    have one : u = 1 := by
      have product : (u - 1) * inner ℝ (facets.normal G) ((a : Space) - c) = 0 := by nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_right gap.ne)
    have parallel : (b : Space) - a = t • ((d : Space) - c) := by
      rw [one, one_smul] at coordinates
      linear_combination (norm := module) coordinates
    exact (net.parallel_petals_disjoint G F G_side F_side c d a b cd ca da ab
      cB dB aB bB cG dG aF bF t parallel).symm.mono interior_subset interior_subset
  · let t := (1 - inner ℝ (facets.normal G) ((a : Space) - center)) /
      inner ℝ (facets.normal G) ((b : Space) - a)
    let o := AffineMap.lineMap (a : Space) (b : Space) t
    have line : o ∈ affineSpan ℝ ({(a : Space), (b : Space)} : Set Space) :=
      mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨t, rfl⟩
    have oB : o ∈ affineSpan ℝ dome.base.val :=
      affineSpan_mono ℝ (show ({(a : Space), (b : Space)} : Set Space) ⊆ dome.base.val from by
        rintro x (rfl | rfl); exacts [aB, bB]) line
    have oF : o ∈ affineSpan ℝ F.val :=
      affineSpan_mono ℝ (show ({(a : Space), (b : Space)} : Set Space) ⊆ F.val from by
        rintro x (rfl | rfl); exacts [aF, bF]) line
    have oG : o ∈ affineSpan ℝ G.val := by
      apply (facets.mem_plane_iff G o).mpr
      have height : inner ℝ (facets.normal G) (o - center) =
          t * inner ℝ (facets.normal G) ((b : Space) - a) +
          inner ℝ (facets.normal G) ((a : Space) - center) := by
        dsimp [o]
        rw [AffineMap.lineMap_apply_module']
        simp only [inner_sub_right, inner_add_right, inner_smul_right]
        ring
      rw [height]
      dsimp [t]
      rw [div_mul_cancel₀ _ parallel_height]
      ring
    exact net.petals_nonoverlap_of_common_plane_point facets F G F_side G_side different
      a b c d ab cd aB bB cB dB aF bF cG dG aG cF o oB oF oG

end SixVertexUnfolding.ConvexPolyhedron.Dome.Development
