# Exact curvature ordering and angular case predicates

Let a triangular face incident to vertex v have edge vectors e,f from v.
Its angle lies strictly between 0 and pi. The complex number

```
z = dot(e,f) + i |cross(e,f)|
```

has that argument and positive modulus `|e||f|`. For a triangular face, the
cross-product norm is the same at all three vertices, so it is the existing
positive face-area variable h in the exact polynomial encoding.

Multiply these numbers over all faces incident to v. The resulting pair
`(X_v,Y_v)` is a positive multiple of `exp(i theta_v)`, where theta_v is the
total incident angle. Strict convexity gives `0 < theta_v < 2 pi`; this
geometric range is essential. Curvature is `kappa_v = 2 pi - theta_v`.

## Comparing curvature

To test `kappa_a >= kappa_b`, test `theta_a <= theta_b`. First distinguish
the upper semicircle `(0,pi]` from `(pi,2pi)` using the imaginary sign and
the negative real ray. Across the two semicircles their order is fixed.
Within the same semicircle, the arguments differ by strictly less than pi,
and their order is the sign of

```
X_a Y_b - Y_a X_b.
```

All expressions are polynomial in the coordinates and positive area variables.
No approximate inverse trigonometric function enters this comparison. Equality
is included by non-strict determinant signs; the semicircle containing pi is
specified explicitly. The zero/2pi ray is excluded by strict convexity.

The same products can be evaluated with outward rational intervals. Unknown
signs or unresolved equalities cause rejection. On the earlier D-lemma witness,
all comparisons establishing vertex 3 as the sharpest vertex are now verified:

```
python3 -m n6.curvature n6/results/d-lemma-counterexample.json --sharpest 3
```

Thus the unrestricted D-lemma fails even under the maximum-curvature apex
hypothesis. The original audit had verified only its unqualified failure.

## Case predicates

Conjugating a vertex product gives a positive multiple of `exp(i kappa_v)`.

- `kappa_a+kappa_b < pi` requires both individual curvatures below pi and
  their product in the open upper half-plane. Equivalently the incident-angle
  products at a,b both have negative imaginary part, and the conjugate product
  has positive imaginary part.
- To test `kappa_a+kappa_b < nu`, where `0<nu<pi`, first require that sum
  below pi, then compare it with nu by an oriented determinant. This expresses
  Case A exactly; its negation includes the equality boundary and Case B.
- `phi+kappa_a < pi` similarly requires `kappa_a<pi` and the product of
  its conjugate vertex product with the face-angle product for phi in the
  open upper half-plane. These are the restricted D-lemma conditions.
- For a sum of positive face angles, multiply in sequence and remember whether
  a full turn has occurred. Adding an angle below pi can cross 2pi only when
  the running product moves from the open lower half-plane to the upper
  half-plane, including the positive real ray. Once a full turn occurs, the
  positive sum can never return below pi. Without a full turn, the final
  product has positive imaginary part exactly when the sum is below pi.

`curvature.py` implements these predicates. Tests exercise pi, curvature ties,
exact full turns, and sums exceeding a full turn using exact rational rays.

## Focused queries

`lemma_query.py` fixes apex 0, antipode 5, and slit vertex 1 in the standard
octahedral graph; graph symmetries justify this labeling for existential failures.
It includes all convex realization constraints and the requested curvature
hypotheses. Local petal–petal and petal–fan failures, opposite-petal failures,
and omitted D-angle regimes are separate targets. Reflection exchanges the
two local petal–fan orientations and the two opposite-petal pairs.

The `--hard-local` flag restricts a local query to
`kappa_slit+kappa_antipode < pi`; it must not be presented as a query for all
of Lemma L. Solver timeouts and memory failures remain unresolved. Even an
UNSAT answer is recorded as a solver result with its exact target and trusted
encoding, not as an independently replayed proof certificate.
