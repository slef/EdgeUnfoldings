# Direct prism-with-one-diagonal investigation

## A complete coordinate chart up to similarities

Let `c=0`, `a=(1,0,0)`, `b=(x,y,0)`, and `c'=(u,v,w)`, with `y,w>0`.
Write the other two vertices as

```
a' = A a + B c'
b' = C b + D c'.
```

The quadrilateral facets `c-a-a'-c'` and `c-b-b'-c'` remain exactly planar.
The vertex labels in the code are `a,b,c,a',b',c' = 0,1,2,3,4,5`.
The other facets are `cab`, `aba'`, `ba'b'`, and `a'b'c'`.

The strict parameter domain for this diagonal choice is

```
y,w,A,B,C,D > 0,
Q = A+B-1 > 0,
R = C+D-1 > 0,
S = D(A-1)-B(C-1) > 0.
```

Every realization of this labeled combinatorial type can be put in this form:
the two quadrilateral planes intersect in the edge `cc'`, and `a,b,c,c'` are
affinely independent. Convexity of each ordered quadrilateral gives its two
positive coefficients and the corresponding Q or R inequality. The two
triangles along diagonal `ba'` give S. Translating c to zero, scaling ca to
unit length, and choosing an orthonormal frame gives the stated coordinates;
a reflection can be used to choose positive w. No affine deformation is being
used to infer preservation of an unfolding.

For sufficiency, direct determinant expansion gives each off-facet support as
`-y w` times one of `1,A,B,C,D,AC,AD,Q,CQ,R A,S`, all positive in this domain.
The two quadrilaterals are ordered and strictly convex by the A,B,Q and C,D,R
conditions. This verifies the exact original-facet combinatorial type.

The chart has nine shape parameters. `families.prism_region` encodes the
coordinates as rational polynomials; `polycert` checks facet coplanarity as
polynomial identities and strict support using outward intervals, independently
of this hand derivation.

## The two-pair tree is not universally successful

The cut tree `ca, cb, cc', c'a', c'b'` leaves only two pairs after the
common-vertex-fan lemma: the two triangular bases, and the two quadrilaterals.
The quadrilaterals can overlap. An exactly checked example is

```
a=(10,0,0)       b=(-30,1,0)       c=(0,0,0)
a'=(25,0,5)     b'=(-60,1,10)     c'=(-30,0,10).
```

After scaling by 1/10 its parameters are
`(-3,1/10,-3,0,1,4,1/2,1,1)`. The checker verifies all original facets and
eight strict separating-axis overlap signs for the two quadrilaterals:

```
python3 -m n6.polycert verify-overlap n6/results/prism-two-pair-failure.certificate.json
```

This eliminates one universal fixed-tree conjecture, not the combinatorial type.
An alternative cut tree `{0-2,0-1,1-4,2-5,3-5}` has an exact nonoverlap
certificate for the example and for every parameter in a nine-dimensional box
of radius `1/1000` around that center:

```
python3 -m n6.polycert verify n6/results/prism-region.certificate.json
```

The regional certificate keeps the two quadrilateral facets exactly planar.
It verifies all 15 face pairs: nine by common uncut vertex fans and six by
separating edges. It is partial coverage, not a proof for the entire chart.

## Relation to Reduction 1 in the overview

The fixed-tree failure does **not** disprove the conditional limit reduction.
That statement assumes a sequence of convex simplicial refinements approaching
the original polytope, each admitting a nonoverlapping cut tree using only
original edges. A constant-tree subsequence has convergent developments, and
positive-area overlap of limiting faces would persist nearby. Uncut diagonals
therefore merge back into the original polygonal facets without overlap.

The example disproves only universal success of the displayed two-pair tree.
The same polyhedron has the independently verified alternative tree above:
in vertex names its cuts are `ca, ab, bb', cc', c'a'`. The existence of suitable
refinements and successful trees avoiding every artificial diagonal remains
unproved for arbitrary shapes. The earlier unconditional claim that the prism
case was already settled by this reduction was unsupported, but this witness
does not establish that the required existence statement is false.

## Next obligation

Independent replay now verifies a larger nine-parameter box using 443 closed
subregions and three trees; see [REGION_COVER.md](REGION_COVER.md) for its exact
bounds and the wider searches that remain incomplete.

The six original-edge degree-four-star candidates are another plausible small
family: 20,000 broad numerical samples found no failure of their union. This
observation is not a proof and does not establish a uniform positive margin.

Find and certify a small family of trees covering this parameter domain,
or derive a geometric rule switching trees when the quadrilaterals or bases
approach overlap. A fixed-tree query alone cannot settle this case. Equality
and unbounded/degenerate parameter regimes cannot be omitted from a global proof.


## Two routes around a quadrilateral: exact failures and a smaller target

There are two degree-four vertices, b=1 and a′=3. Each lacks an edge to one
opposite corner of an original quadrilateral. A candidate near-star cuts all
four edges at the chosen apex, then connects the missing vertex by an edge
through either of the other quadrilateral corners. These are four trees:

| Apex | Missing neighbor | Route via |
| --- | --- | --- |
| b=1 | c′=5 | c=2 or b′=4 |
| a′=3 | c=2 | a=0 or c′=5 |

Each tree leaves four face-pair obligations after the shared-vertex lemma.
`trees.quadrilateral_path_stars` constructs exactly these original-edge trees.

**Both routes at a fixed apex can fail.** At the following integer points,
the two b=1 trees have certified positive-area overlap; both a′=3 trees have
certified simple nets:

```
a=(10000,0,0)       b=(-2300,2000,0)     c=(0,0,0)
a′=(-32950,17875,325) b′=(-12352,5980,100) c′=(-11800,5500,100).
```

All original facets, planarity, and strict supporting planes are checked.
The four `prism-path-apex*-via*.certificate.json` files and
`prism-two-paths.verification.json` retain the exact results. This refutes a
rule that fixes one degree-four apex and always expects one of its two routes
to work. It does not refute the four-tree family.

**Even at the sharper degree-four apex, the shorter route can fail.** A
smaller second example is

```
a=(50,0,0)     b=(-5,10,0)   c=(0,0,0)
a′=(-4,0,24)   b′=(-39,1,11) c′=(-35,0,10).
```

Exact angle comparisons prove kappa(a′)>kappa(b). The route a′–c′–c is
strictly shorter than a′–a–c, but its unfolding has positive-area overlap.
The longer route at the same apex gives a certified simple net. Thus a
future two-route argument must compare the resulting faces; minimizing the
boundary-path length is insufficient. Replay without numerical packages:

```
python3 -m n6.prism_paths n6/results/prism-shorter-path-failure.certificate.json
python3 -m n6.polycert verify n6/results/prism-longer-path-success.certificate.json
python3 -m unittest n6.tests.test_prism_paths
```

**Still only a conjectural target:** take the sharper of b and a′, and allow
both quadrilateral routes. A new 60,000-shape numerical run found no failure
of that pair, while the shorter-route rule failed 395 times. A separate
50,000-shape run found no failure of the four-tree union. These searches omit
limits and use tolerances; neither proves universal success or a positive
uniform margin. Results and seeds are saved in `prism-selected-quad-star-search.json`
and `prism-quad-star-search.json`. Reproduce the former with

```
durer_small_n/.venv/bin/python -m n6.original_star_probe --family quadrilateral \
  --samples 60000 --seconds 500 --seed 6090918 \
  --output /tmp/prism-selected-quad-star-search.json
```

The exact finite certificates above are independent of these sampled counts.
