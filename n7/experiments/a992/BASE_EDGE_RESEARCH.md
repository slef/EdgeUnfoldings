# E/235 continuation: extend the base, then use the five-vertex proof

12 September 2026. The positive result is written in
[A992_BASE_EDGES.md](../../A992_BASE_EDGES.md). No floating search is a
premise of that proof.

The E/235 hinge path reduces P to quadrilateral 6152. Extending 61 beyond
1 and 25 beyond 5 supplies a new fan center exactly when angle162 +
angle625 < pi. All six supporting planes of the resulting five-vertex
bipyramid can be checked from the original supporting planes and the base
orientation. The old obtuse-petal lemma then applies without modifying a
cut in the final original-edge net. Parallel rays are handled by a strict
convexity-preserving perturbation with the petal angle held fixed.

The exact converging and parallel examples both have genuine Left overlap
and an inward corner at 0, so the cone theorem puts them in R0. The original
exact counterexample has divergent hinges and remains a real member of the
unresolved R0 family, even though Right works on that particular shape.

## Other investigations retained

The general obtuse-petal search for the E/235 pair made 24,000 attempts,
with 2,858 valid numerical shapes and 1,921 with an obtuse E angle at 0.
It found no robust E/235 overlap. This motivates a stronger question but
proves no universal statement. The seed, parameters, and scores are saved
in `a992-e235-obtuse-search.json`.

A different possible separator was the perpendicular bisector between the
copy of vertex 3 in E and its copy in 235. The source-image Voronoi structure
is established for a shortest-path star; see the primary paper
[Aronov and O'Rourke](https://doi.org/10.1007/BF02293047). The proposed use here still needed an extra claim placing the
new 0-copy on the correct side of that bisector.

The 65,000-attempt numerical search found an obtuse-E example violating
that extra point-placement inequality, while E and 235 themselves remained
separated. It had a negative normalized squared-distance difference about
-0.0212. The example is outside R0, so it does not refute a version using
all the R0 hypotheses. These are floating observations, not exact
counterexamples. No Voronoi claim was used in the positive proof.

A second auxiliary triangle, 026 attached to base diagonal 26, shares
vertex 6 with E along its uncut path and avoids 235 by the neighborhood
of triangle 256 in a smaller hull. It may be useful for a containment
argument in the divergent branch. Unlike the earlier E/135 proof, the
angle between 63 and 65 can now involve two unfolded faces; it must not
be treated as a single spherical-link side. The earlier positive identity
therefore cannot simply be copied with that substitution.

## Next target

In R0 with converging or parallel hinges, E/135 and E/235 are proved safe;
only E/Q remains. For divergent hinges, E/235 still needs a proof as well.
A useful next choice is either the remaining E/Q pair in this newly
reduced family or a containment argument for the divergent E/235 case.
Do not apply the auxiliary-bipyramid construction to an intersection behind
6 and 2: it fails its supporting-plane hypotheses there.
