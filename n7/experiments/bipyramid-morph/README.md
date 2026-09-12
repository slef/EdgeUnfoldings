# Bipyramid insertion discoveries, 13 September 2026

The two archived searches use floating predicates only. Their tolerances
are for discovery, never proof. Both generate planar equator examples,
so their sample scope excludes nonplanar equators.

The first search found a fixed-tree failure with a nonminimum inserted
vertex (round 34). It is retained, but the main proof page uses the stronger
minimum-vertex failure from seed 913509, round 8929. The latter search
considers only equator minima and neighbor-edge reductions. Neither search
claims exhaustive coverage, and neither was continued after its first hit.

The minimum example was rounded to five decimal places and independently
verified with exact rational interval predicates in `../../bipyramid_morph.py`.
Its final rational coordinates, minimum-curvature ordering, endpoint
interior witness, and all-parameter successful alternative net are in
`../../results/bipyramid-morph.json`.

The separate simple pole-edge example was constructed directly with rational
coordinates. Its eight-interval proof is in the same file. The written
convexity and normal-cone proofs apply to general, nonplanar bipyramids;
the numerical sample distribution is not a premise of either proof.

Run from the worktree root with the n7 requirements installed. The archived
scripts write their discovered result to a named file in `/private/tmp`.
