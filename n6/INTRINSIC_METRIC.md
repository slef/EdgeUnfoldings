# What shared edge lengths add to the Case B problem

Continuation on 9 September 2026. The blanket individual-apex bound is now
refuted by an actual convex example (see the final section). The universal
octahedron argument and the separate remote-apex question remain open. The
historical reductions below explain why two simplified metric models were
insufficient; the later exact axis-closure test supplies another condition.

## The older angle countermodel cannot even close its spokes

The rational angle assignment in `results/apex-angle-relaxation.json` satisfies
the triangle sums, strict positive curvatures, the strict convex-vertex cone
inequalities, and both strict curvature rankings. Nevertheless it has
`Sigma_W+a < pi`, so those linear facts do not imply the proposed exclusion.

It now has a particularly simple, exact explanation of its metric failure.
In every V triangle, its angle `aV_i` is strictly larger than `aVp_i`.
The opposite sides would therefore satisfy

```
s_1 > s_0,  s_2 > s_1,  s_3 > s_2,  s_0 > s_3.
```

This is impossible. The W triangles force the same impossible cycle among the
four r spokes. This argument uses rational comparisons of the given angles and
the elementary larger-angle/larger-side property of a Euclidean triangle. It
does not rely on rounded sine values or on a failed coordinate reconstruction.
The angle checker now records both obstructions.

```
python3 -m n6.angle_relaxation n6/results/apex-angle-relaxation.json
```

## A complete intrinsic compatibility condition

For arbitrary positive face angles with each triangle sum equal to pi, define

```
rho_i = sin(aV_i) / sin(aVp_i)
eta_i = sin(bW_i) / sin(bWp_i)
t_i   = sin(nu_i) / sin(aVp_i)
z_i   = sin(omega_i) / sin(bWp_i)
c_i   = t_i / z_i.
```

Here `s_i=|vu_i|`, `r_i=|wu_i|`, and `ell_i=|u_i u_{i+1}|`. The sine rule gives

```
s_{i+1} = rho_i s_i,       r_{i+1} = eta_i r_i,
ell_i = t_i s_i = z_i r_i, hence r_i = c_i s_i.
```

Consequently the following one product equation and four cyclic equations are
necessary and sufficient for these eight triangles to share consistent,
strictly positive edge lengths:

```
product_i rho_i = 1,
c_{i+1} rho_i = c_i eta_i       for i=0,1,2,3, indices modulo four.
```

For sufficiency, choose `s_0>0`, construct the other s spokes by the rho
recurrence, put `r_i=c_i s_i`, and put `ell_i=t_i s_i`. The product equation
closes the s cycle; the cyclic equations enforce all W spoke ratios and their
closure. The sine rule then realizes each prescribed Euclidean triangle with
these sides. This constructs a glued intrinsic metric, **not** a convex
polyhedron with the eight prescribed original facets.

## Metric compatibility does not replace convex-vertex constraints

A new exact rational metric witness matches all twelve edge lengths, has
strictly positive curvature at all six vertices, satisfies strict H and R,
and still has `Sigma_W+a < pi`. However, it violates a necessary cone
inequality at v and at two equator vertices: an incident face angle is larger
than the sum of the other three. Thus it cannot be a convex octahedron with
these original triangles. It supplies a check on the relaxation, not a
counterexample to the geometric conjecture or to edge unfolding.

The saved lengths are exact rational numbers obtained by rounding an optimizer
proposal and then independently checking that rational input. The rounding
and the optimizer are not used in the proof verdict.

```
python3 -m n6.intrinsic verify n6/results/intrinsic-without-cone.certificate.json
```

The checker proves triangle existence from positive squared sides and positive
Heron expressions, tracks incident angle sums before accepting positive
curvature, and compares angles by outward rational bounds on complex products.
Its report proves the three cone violations separately. Requiring the cone
conditions makes it reject this witness.

## A smaller algebraic search retaining both ingredients

`intrinsic.py query` uses twelve squared edge lengths and eight positive
four-times-area variables. Each triangle contributes the quadratic equation

```
h^2 = 4 q_b q_c - (q_b+q_c-q_a)^2.
```

Its three angle vectors are `(q_b+q_c-q_a, h)` and their cyclic analogues.
All shared sides are identical variables. The query retains positive curvature,
the convex-vertex cone inequalities, H, and R, and asks whether `Sigma_W+a<pi`
is possible. Its default slit index is 3 and its triple start is 0; a result
for this query alone must not silently stand in for the other triple/slit
orientation. The opposite orientation is selected with `--slit-index 0`.

```
python3 -m n6.intrinsic query --output n6/results/intrinsic-apex-query.json --seconds 900
```

Full turns in angle products are explicitly tracked. Without this check,
modulo-2-pi products could incorrectly accept negative-curvature metrics.
Boundary and repeated-wrap cases are covered by exact tests. Solver results
remain separate from independently replayed certificates; numerical searches
and solver timeouts do not establish the desired universal inequality.

The first lifted query used 244 auxiliary variables and returned `unknown`
after approximately 904 seconds (900-second solver limit). It proves neither
existence nor nonexistence of a countermodel. The exported formula and outcome
are retained in `results/intrinsic-apex-query.smt2` and the adjacent JSON file.

The opposite slit orientation was also queried without lifting. It returned
`unknown` after approximately 695 seconds with a 600-second solver limit.
Solver limits can overrun during internal processing. The driver now reuses
the repository's separate-process time and memory guard; its default wall
limit is the requested solver time plus 30 seconds. A deliberate short-limit
check confirmed termination with an explicit unresolved verdict.

## Further correction: even all local checks do not enforce global closure

The second continuation found `intrinsic-with-cone.certificate.json`. Unlike
the earlier metric example, it satisfies **all six strict cone inequalities**,
as well as shared lengths, positive curvatures, and strict H and R. It has
`Sigma_W+a<pi` for triple 0 with slit 0. Exact rational bounds verify every
claim; the earlier slit-3 searches must not be conflated with this orientation.

Nevertheless, these lengths cannot form a convex octahedron with the prescribed
original facets. The [axis-closure certificate](AXIS_CLOSURE.md) proves this on
five closed intervals covering every possible distance between v and w.
This supplies a specific missing global condition in the intrinsic relaxation.

More decisively, a subsequent **actual convex integer-coordinate example**
refutes the individual-apex exclusion itself while its selected net remains
simple. See the [Case B correction](CASE_PARTITION.md). Adding more realization
constraints cannot prove that false stronger statement. The remaining useful
question concerns the two petals jointly, with each slit orientation explicit.
