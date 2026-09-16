import SixVertexUnfolding.Geometry.TerminalSourceImage

/-! A terminal source copy can be recovered from any earlier point in the
target face. This removes dependence on the last crossing time. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set

variable {P : ConvexPolyhedron} {a b : Space}

/-- Exact affine coordinates between two visits to a face. -/
theorem face_coordinates_eq_lineMap (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (speed : LipschitzWith path.length.toNNReal path.curve)
    (F : P.Face) (s t : unitInterval) (ordered : s < t)
    (hs : path.curve s ∈ F.val) (ht : path.curve t ∈ F.val)
    (u : unitInterval) (hu : u ∈ Icc s t) :
    P.faceCoordinates F (path.curve u) =
      AffineMap.lineMap (P.faceCoordinates F (path.curve s)) (P.faceCoordinates F (path.curve t))
        (((u : ℝ) - (s : ℝ)) / ((t : ℝ) - (s : ℝ))) := by
  have middle := F.convex.segment_subset hs ht
    (path.shortest_portion_range shortest finite F s t ordered.le hs ht u hu)
  have distance (v w : unitInterval) (hv : path.curve v ∈ F.val) (hw : path.curve w ∈ F.val)
      (vw : v ≤ w) : dist (P.faceCoordinates F (path.curve v)) (P.faceCoordinates F (path.curve w)) =
        path.length.toReal * ((w : ℝ) - (v : ℝ)) := by
    rw [P.faceCoordinates_rigid F _ hv _ hw, ← P.surfaceDist_eq_dist_in_face F hv hw,
      path.surfaceDist_along shortest finite speed]
    congr 1
    change dist (v : ℝ) (w : ℝ) = _
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show (v : ℝ) ≤ (w : ℝ) from vw))]
  exact point_eq_lineMap_of_distance_ratios _ _ _ s u t path.length.toReal ordered hu.1 hu.2
    (distance s u hs middle hu.1) (distance u t middle ht hu.2) (distance s t hs ht ordered.le)

/-- A terminal affine formula extends backwards as far as the route stays in that face. -/
theorem terminal_formula_extends (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (speed : LipschitzWith path.length.toNNReal path.curve)
    (F : P.Face) (target : b ∈ F.val) (source : Plane)
    (start : unitInterval) (before : start < 1)
    (tail : ∀ u ∈ Icc start 1, P.faceCoordinates F (path.curve u) =
      AffineMap.lineMap source (P.faceCoordinates F b) (u : ℝ))
    (t : unitInterval) (t_before : t < 1) (inside : path.curve t ∈ F.val) :
    P.faceCoordinates F (path.curve t) = AffineMap.lineMap source (P.faceCoordinates F b) (t : ℝ) := by
  obtain ⟨u, after, u_before⟩ := exists_between (max_lt before t_before)
  have tu : t < u := (le_max_right start t).trans_lt after
  have target' : path.curve 1 ∈ F.val := by simpa only [path.curve.target] using target
  have affine := path.face_coordinates_eq_lineMap shortest finite speed F t 1 t_before inside target'
    u ⟨tu.le, u_before.le⟩
  have terminal := tail u ⟨(le_max_left start t).trans after.le, u_before.le⟩
  have nonzero : 1 - (t : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr (show (t : ℝ) < 1 from t_before))
  let r : ℝ := ((u : ℝ) - (t : ℝ)) / (1 - (t : ℝ))
  have r_before : r < 1 := (div_lt_one (sub_pos.mpr (show (t : ℝ) < 1 from t_before))).mpr
    (sub_lt_sub_right (show (u : ℝ) < 1 from u_before) _)
  have coefficient : (1 - r) * (1 - (t : ℝ)) = 1 - (u : ℝ) := by dsimp [r]; field_simp [nonzero]; ring
  have second_coefficient : (1 - r) * (t : ℝ) + r = (u : ℝ) := by
    dsimp [r]; field_simp [nonzero]; ring
  have nested : AffineMap.lineMap (AffineMap.lineMap source (P.faceCoordinates F b) (t : ℝ))
      (P.faceCoordinates F b) r = AffineMap.lineMap source (P.faceCoordinates F b) (u : ℝ) := by
    simp only [AffineMap.lineMap_apply_module, smul_add, smul_smul]
    rw [add_assoc, ← add_smul, coefficient, second_coefficient]
  apply lineMap_left_unique _ _ (P.faceCoordinates F b) r r_before.ne
  simpa only [path.curve.target] using affine.symm.trans (terminal.trans nested.symm)

/-- At a target belonging to just one face, every earlier point of that face recovers a fixed source copy. -/
theorem source_image_at_face_visit (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (speed : LipschitzWith path.length.toNNReal path.curve)
    (avoids : ∀ u : unitInterval, 0 < u → u < 1 → path.curve u ∉ P.vertices)
    (F : P.Face) (unique : ∀ G : P.Face, b ∈ G.val → G = F)
    (t : unitInterval) (before : t < 1) (inside : path.curve t ∈ F.val) :
    ∃ source ∈ P.sourceImages a F, P.faceCoordinates F (path.curve t) =
      AffineMap.lineMap source (P.faceCoordinates F b) (t : ℝ) := by
  obtain ⟨code, start, start_before, tail⟩ := path.exists_terminal_source_code shortest finite speed avoids
  have target := (tail 1 ⟨unitInterval.le_one', le_rfl⟩).1
  rw [path.curve.target] at target
  have same := unique (code.face code.last) target
  refine ⟨code.sourceImage a, ⟨⟨code, same⟩, rfl⟩, ?_⟩
  apply path.terminal_formula_extends shortest finite speed F (same ▸ target) _ start start_before
    (fun u hu => ?_) t before inside
  simpa only [same] using (tail u hu).2

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
