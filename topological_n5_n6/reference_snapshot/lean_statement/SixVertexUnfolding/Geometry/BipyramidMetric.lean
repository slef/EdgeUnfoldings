import SixVertexUnfolding.Geometry.BipyramidDevelopment
import SixVertexUnfolding.Geometry.BipyramidWeights
import SixVertexUnfolding.Geometry.RadonMetric

/-! The strict source-copy comparisons between opposite caps, derived from the Radon weights. -/

namespace SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices.Development

variable {P : ConvexPolyhedron} {B : P.BipyramidVertices}
    {triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3}
    {source : Fin 3} (net : B.Development triangles source)

/-- The two bases give the same coordinates to their two equator endpoints. -/
theorem base_equator_agreement (upper : Bool) (i : Fin 3) (different : i ≠ source) :
    (net.cap upper).place source (B.equatorVertex i) =
      (net.cap (!upper)).place source (B.equatorVertex i) := by
  have agree := net.bases_joined (B.equatorVertex i)
    ⟨(B.equator_mem_face triangles true source i).mpr different,
      (B.equator_mem_face triangles false source i).mpr different⟩
  cases upper
  · exact agree.symm
  · exact agree

/-- Either ordering of the poles satisfies the central strict distance comparison. -/
theorem base_poles_farther (upper : Bool) :
    dist (B.poleVertex upper : Space) (B.poleVertex (!upper) : Space) <
      dist ((net.cap upper).place source (B.poleVertex upper))
        ((net.cap (!upper)).place source (B.poleVertex (!upper))) := by
  cases upper
  · simpa only [poleVertex, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_eq,
      dist_comm] using net.poles_farther
  · exact net.poles_farther

/-- All triangles on a cap retain the same copy of their pole. -/
theorem petal_pole_agreement (upper : Bool) (missing : Fin 3) :
    (net.cap upper).place missing (B.poleVertex upper) =
      (net.cap upper).place source (B.poleVertex upper) :=
  (net.cap upper).joined missing (B.poleVertex upper) (B.pole_mem_face triangles upper missing)
    (B.pole_mem_face triangles upper source)

/-- A retained equator endpoint has the same position on the petal and on its base. -/
theorem petal_equator_agreement (upper : Bool) (missing i : Fin 3)
    (in_petal : i ≠ missing) (in_base : i ≠ source) :
    (net.cap upper).place missing (B.equatorVertex i) =
      (net.cap upper).place source (B.equatorVertex i) :=
  (net.cap upper).joined missing (B.equatorVertex i)
    ((B.equator_mem_face triangles upper missing i).mpr in_petal)
    ((B.equator_mem_face triangles upper source i).mpr in_base)

/-- Every source copy is strictly farther from the opposite pole than the original source was. -/
theorem opposite_pole_farther (size : P.vertices.card = 5) (upper : Bool) (missing : Fin 3)
    (petal : missing ≠ source) :
    dist (B.poleVertex (!upper) : Space) (B.equatorVertex source : Space) <
      dist ((net.cap (!upper)).place source (B.poleVertex (!upper)))
        ((net.cap upper).place missing (B.equatorVertex source)) := by
  obtain ⟨k, km, ks, _⟩ := remaining_equator_index missing source petal
  obtain ⟨a, b, s, u, v, ha, hb, hs, _, hv, total, balance⟩ :=
    B.exists_positive_radon_weights size (!upper) source k missing ks.symm petal.symm km
  simp only [Bool.not_not] at balance
  let own := (net.cap upper).place source
  let other := (net.cap (!upper)).place source
  let copy := (net.cap upper).place missing
  have pole_in := B.pole_mem_face triangles upper source
  have opposite_in := B.pole_mem_face triangles (!upper) source
  have k_in := (B.equator_mem_face triangles upper source k).mpr ks
  have missing_in := (B.equator_mem_face triangles upper source missing).mpr petal
  have k_in_other := (B.equator_mem_face triangles (!upper) source k).mpr ks
  have missing_in_other := (B.equator_mem_face triangles (!upper) source missing).mpr petal
  have source_in_petal := (B.equator_mem_face triangles upper missing source).mpr petal.symm
  have pole_in_petal := B.pole_mem_face triangles upper missing
  have k_in_petal := (B.equator_mem_face triangles upper missing k).mpr km
  have k_agree : own (B.equatorVertex k) = other (B.equatorVertex k) := net.base_equator_agreement upper k ks
  have missing_agree : own (B.equatorVertex missing) = other (B.equatorVertex missing) :=
    net.base_equator_agreement upper missing petal
  apply radon_missing_distance_gt a b s u v
    (B.poleVertex (!upper)) (B.poleVertex upper) (B.equatorVertex source)
    (B.equatorVertex k) (B.equatorVertex missing)
    (other (B.poleVertex (!upper))) (own (B.poleVertex upper))
    (copy (B.equatorVertex source)) (own (B.equatorVertex k)) (own (B.equatorVertex missing))
    ha hb hs hv.le total balance
  · rw [k_agree]
    exact (net.cap (!upper)).rigid source _ opposite_in _ k_in_other
  · rw [missing_agree]
    exact (net.cap (!upper)).rigid source _ opposite_in _ missing_in_other
  · exact (net.cap upper).rigid source _ pole_in _ k_in
  · exact (net.cap upper).rigid source _ pole_in _ missing_in
  · exact (net.cap upper).rigid source _ k_in _ missing_in
  · have rigid := (net.cap upper).rigid missing _ pole_in_petal _ source_in_petal
    rw [net.petal_pole_agreement] at rigid
    exact rigid
  · have rigid := (net.cap upper).rigid missing _ source_in_petal _ k_in_petal
    rw [net.petal_equator_agreement upper missing k km ks] at rigid
    exact rigid
  · cases upper
    · change dist (B.top : Space) (B.bottom : Space) <
        dist ((net.cap true).place source B.top) ((net.cap false).place source B.bottom)
      exact net.poles_farther
    · change dist (B.bottom : Space) (B.top : Space) <
        dist ((net.cap false).place source B.bottom) ((net.cap true).place source B.top)
      rw [dist_comm (B.bottom : Space) (B.top : Space),
        dist_comm ((net.cap false).place source B.bottom) ((net.cap true).place source B.top)]
      exact net.poles_farther
  · have farther := (net.cap upper).farther missing petal (B.equatorVertex missing) missing_in
      (fun member => (B.equator_mem_face triangles upper missing missing).mp member rfl)
    simpa only [dist_comm] using farther.le

end SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices.Development
