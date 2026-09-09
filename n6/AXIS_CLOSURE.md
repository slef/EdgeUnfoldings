# Matching triangles must also close around the antipodal axis

This is a **necessary condition** for twelve lengths to be the original edges
of a strictly convex octahedron. It is not asserted sufficient for convexity.
The exact example below passes all the earlier intrinsic/local checks but
fails this global condition. Separately, the [actual convex apex-entry example](CASE_PARTITION.md)
refutes the stronger individual-apex claim; closure does not rescue that claim.

## Derivation

Put v=(0,0,0), w=(0,0,d), with d>0, and let t=d². Write s_i, r_i, l_i for the
**squared** lengths |vu_i|², |wu_i|², |u_i u_(i+1)|². (The earlier prose about
sine-rule compatibility uses unsquared s and r; this page uses squared inputs
throughout.) The height and squared radius of u_i about the axis satisfy

```
z_i = (s_i-r_i+t)/(2d),
4t rho_i² = A_i = 4t s_i - (s_i-r_i+t)².
```

The dot product of the two projected equator vectors, multiplied by 4t, is

```
B_i = 2t(s_i+s_(i+1)-l_i) - (s_i-r_i+t)(s_(i+1)-r_(i+1)+t).
C_i = A_i A_(i+1) - B_i².
```

Strict convexity and the prescribed original facets require A_i>0 and C_i>0.
Indeed, w is strictly off the supporting plane of every face (v,u_i,u_(i+1)),
so the tetrahedron (v,w,u_i,u_(i+1)) has nonzero volume. All four projected
oriented areas have the same sign; reverse the viewing direction if needed.
Thus the positive azimuth turn gamma_i between successive equator vertices
lies strictly between 0 and pi and is represented by

```
Z_i = B_i + i sqrt(C_i).
```

Its magnitude is sqrt(A_i A_(i+1)); division by that positive magnitude would
give cos(gamma_i)+i sin(gamma_i). After the four turns we must return to the
same ray. Consequently

```
Im(product_i Z_i) = 0,
Re(product_i Z_i) > 0.
```

Four strictly positive turns, each below pi, sum to a number in (0,4pi).
The displayed closure equation therefore forces their sum to be exactly 2pi.
This does not assume that the resulting surface is convex merely because it
closes; the condition is used only in the necessary direction.

## A complete one-variable exclusion certificate

Every possible d lies in the intersection of the four triangle-inequality
intervals [|sqrt(s_i)-sqrt(r_i)|, sqrt(s_i)+sqrt(r_i)]. Squaring gives a closed
outer interval for t. All possible strictly convex realizations must occur
inside it. Including its endpoints avoids any hidden gap in the coverage.

The checker subdivides this interval and proves one of the following on each
closed child:

- Some A_i is nonpositive throughout; or
- Some C_i is nonpositive throughout; or
- The imaginary part of the closure product is strictly positive or strictly
  negative throughout every potentially feasible point in the child.

If a C interval straddles zero, its lower bound is clipped to zero before
bounding its square root. This is safe: only actual candidates with C_i>0
matter. No candidate value is removed by the clipping. Polynomial bounds use
an exact rational Taylor shift to the child midpoint, followed by outward
interval evaluation; the midpoint expansion is an identity, not a numerical fit.

For `intrinsic-with-cone.certificate.json`, the root interval is

```
18.5986050121 <= t <= 18.9431246169.
```

Five closed intervals suffice. Four have an impossible tetrahedron square;
one has a strictly positive imaginary closure product. This proves that no
strictly convex octahedron has these twelve numbers as its original edge
lengths. The separate intrinsic checker verifies all eight Euclidean
triangles, shared edges, positive curvatures, all six strict cone conditions,
and both strict rankings. There is no contradiction: local compatibility
is weaker than original-facet realization.

```
python3 -m n6.intrinsic verify n6/results/intrinsic-with-cone.certificate.json
python3 -m n6.axis_closure verify n6/results/intrinsic-axis-nonclosure.certificate.json
```

The verifier reconstructs the root bounds and every closed subdivision from
the lengths. Removing part of the root, changing a sign, or using an invalid
split is rejected. A regular octahedron is an explicit positive control:
s_i=r_i=l_i=1, t=2, A_i=4, B_i=0, sqrt(C_i)=4, so the product is positive real.

## Use in further searches

`n6.intrinsic query --axis-closure` adds one opposite-vertex distance variable,
four positive square-root variables, and the exact closure equations. The
first such unrestricted query returned `unknown` because of its 1 GB memory
limit after about 159 seconds. That outcome proves nothing. An independent
coordinate search then produced the actual convex apex-entry example, so a
universal exclusion of the individual-apex event is no longer a valid target.


For the latest symbolic query the same condition is encoded with two
opposite two-turn arcs. Put `P=Z_0 Z_1`, `Q=Z_2 Z_3`. Their positive magnitudes
have ratio `A_1/A_3`, so closure is equivalent to

```
A_3 Re(P) = A_1 Re(Q),
A_3 Im(P) = -A_1 Im(Q).
```

The positive A and square-root conditions are retained. This avoids expanding
the four-turn product; the independent nonclosure verifier still checks the
original product directly. The angle target is also shortened: using the
middle triangle's angle sum, `Sigma_W+a<pi` becomes
`a+b_W0+b_W2 < omega_1`. A branch guard puts the three-angle sum below pi
before a complex determinant compares it to omega_1. The remote/slit-3 query
with these simplifications still returned `unknown` (1 GB memory limit,
about 44 seconds). It provides no proof of the remaining remote-apex bound.
