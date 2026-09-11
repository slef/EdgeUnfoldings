# The original prism two-pair net has only one unresolved face pair

12 September 2026. Written geometric reduction, pending independent review.
This is not a complete prism theorem. It uses the published shortest-path
star-unfolding theorem explicitly cited in COFACIAL_STAR_REDUCTION.md.

Use faces A=021, B=0352, C=013, D=1254, E=143, F=345 and the original
cut tree T={02,12,25,35,45}. Then every face pair except **B/D** has disjoint
interiors, for every genuine convex realization of this prism type.
In particular, the triangular caps **A/F are always disjoint**. No end
curvature bound is needed for this conclusion.

## Proof by a reference star at the degree-three vertex 2

The paths 20,21,25 are original edges. The straight diagonals 23 and 24
lie inside the original convex quadrilaterals B and D respectively. Each
of the five paths is a shortest surface path: it realizes the Euclidean
chord distance between its endpoints. Their interiors are disjoint.
Cutting these paths is a shortest-path star unfolding at vertex 2, and
therefore has no face-interior overlap.

Split B along 23, giving triangles 203 and 235. Each is a leaf of the
reference face tree, attached along 03 or 35: the other two edges are
cuts at 2. Similarly D splits along 24 into leaf triangles 214 and 245,
attached along 14 or 45. Delete all four leaf triangles. What remains
is exactly the connected chain of original triangles

    A -- C -- E -- F,

with hinges 01,13,34. That whole chain is nonoverlapping as a subset of
the reference star.

In the proposed original-edge tree T, B is a leaf attached to C along
03, and D is a leaf attached to E along 14. Removing B and D leaves the
same chain A--C--E--F, with the same hinges and hence the same relative
planar development, up to rigid motion/reflection. Thus all six pairs
among these four triangular faces, including A/F, have disjoint interiors.

The thirteen pairs previously proved by a common uncut vertex are still
safe by the vertex-sector argument. Their union with these six inherited
pairs contains fourteen of all fifteen pairs. The only pair left is B/D.
The comparison diagonals 23,24 are not final cuts: both original quads
remain whole in T. The theorem is valid without a curvature ranking or
positive clearance. Boundary contact is allowed.

## Consequences and limits

The two-sharp-end theorem PRISM_TWO_SHARP_ENDS.md can now omit its separate
triangular-cap argument. Only its B/D proof is needed to finish that family.
The earlier exact two-pair failures involve B/D and remain counterexamples
to the unrestricted tree. No claim that T always works is made.

The reduction suggests comparing two candidates when vertex 2 is sharp:
T and N=star(1)+25. If N's cofacial Case A pair is safe, N works. Otherwise
T needs just B/D. This is a new single-pair switching target, not a proof
that either candidate must work. The same comparison reflects at vertex 5.
