import Mathlib

namespace SixVertexUnfolding

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- Affine dimension: 1 for an edge, 2 for a face.
noncomputable def affineDimension (s : Set Space) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ s).direction

-- A bounded, genuinely three-dimensional convex polyhedron.
structure ConvexPolyhedron where
  vertices : Finset Space
  solid : (interior (convexHull ℝ (vertices : Set Space))).Nonempty
  vertices_exact :
    (vertices : Set Space) =
      (convexHull ℝ (vertices : Set Space)).extremePoints ℝ

def ConvexPolyhedron.body (P : ConvexPolyhedron) : Set Space :=
  convexHull ℝ (P.vertices : Set Space)

-- A whole two-dimensional intersection with a supporting plane.
def ConvexPolyhedron.IsFace (P : ConvexPolyhedron) (F : Set Space) : Prop :=
  affineDimension F = 2 ∧
  ∃ (n : Space) (h : ℝ), n ≠ 0 ∧
    (∀ x ∈ P.body, inner ℝ n x ≤ h) ∧
    F = {x ∈ P.body | inner ℝ n x = h}

-- ALL faces, each represented once by its set of points.
def ConvexPolyhedron.Face (P : ConvexPolyhedron) :=
  {F : Set Space // P.IsFace F}

-- Two distinct faces meet along an original edge exactly when
-- their intersection has affine dimension one.
def ConvexPolyhedron.ShareEdge (P : ConvexPolyhedron) (F G : P.Face) : Prop :=
  affineDimension (F.val ∩ G.val) = 1

structure EdgeUnfolding (P : ConvexPolyhedron) where
  place : P.Face → Space → Plane
  hinges : SimpleGraph P.Face
  tree : hinges.IsTree
  original_edges : ∀ F G, hinges.Adj F G → P.ShareEdge F G
  rigid : ∀ F, ∀ x ∈ F.val, ∀ y ∈ F.val,
    dist (place F x) (place F y) = dist x y
  joined : ∀ F G, hinges.Adj F G → ∀ x ∈ F.val ∩ G.val,
    place F x = place G x
  nonoverlap : ∀ F G, F ≠ G →
    Disjoint (interior (place F '' F.val))
             (interior (place G '' G.val))

def ConvexPolyhedron.HasEdgeUnfolding (P : ConvexPolyhedron) : Prop :=
  Nonempty (EdgeUnfolding P)

end SixVertexUnfolding
