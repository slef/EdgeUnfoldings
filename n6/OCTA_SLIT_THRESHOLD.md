# A direct curvature threshold replaces the maximum-slit ranking

11 September 2026. Written geometric extension of the selected-net theorem.
Independent mathematical review is still needed. Numerical experiments and
the explicit-domain certificates are not premises of this proof.

## The rule

Let v,w be opposite vertices of a convex octahedron, and c an equator
vertex. Suppose either

* kappa_v>=pi, or
* every vertex curvature is at most pi.

If

    2*kappa_c+kappa_w >= pi,                         (T)

then cutting star(v) and wc gives a nonoverlapping net. The source need
not be globally sharpest, and c need not maximize equator curvature.
Equality in (T) and in either source-curvature condition is included.

Under H the source condition always holds: either the maximum curvature
is at least pi or all curvatures are at most pi. Thus **every slit satisfying
(T) is safe at the sharpest source**, even when several slits pass it.
The original every-slit Lemma F still asks about slits failing (T).

At least one slit passes (T). Indeed, for an equator maximum c,

    4*kappa_c >= 4*pi-kappa_v-kappa_w,
    2*kappa_c+kappa_w >= 2*pi-kappa_v/2+kappa_w/2 > pi,

since kappa_v<2*pi and kappa_w>0. This recovers the earlier R rule, but
does not require choosing a maximum when a different endpoint passes (T).

## 1. All three local pairs are safe under (T)

The through-fan part of [Lemma L](LEMMA_L_PROOF.md) works whenever the
source curvature is at least pi or the fan curvature is at most pi.
Both source alternatives above imply one of these conditions; no ranking
is used in this part.

Across the slit, the curvature-gate argument already gives strict angular
separation if kappa_c+kappa_w>=pi. Otherwise at most one flank patch
extends across the gap. Reflect so it is the first patch, with extension B.
If B<kappa_w, the cones are separated strictly. If B>=kappa_w, write
rho=the inward patch corner at c minus pi. The patch identity gives

    kappa_w <= B < rho < pi-kappa_c.

Condition (T) therefore implies

    0 < rho-kappa_w/2 < pi-kappa_c-kappa_w/2 <= pi/2.

The last upper bound may be equality, but the bound on rho is strict.
Consequently the same slit-edge determinant from the complete L proof is
strictly negative:

    det(d,b-c) = -2*r*sin(kappa_w/2)*cos(rho-kappa_w/2) < 0,

where r=|wc|, b is the other slit copy, and d is the inward petal's
cut-edge direction. The opposite patch lies strictly on the other side of
that cut edge, exactly as in Section 4 of LEMMA_L_PROOF.md. This separates
both affected local pairs. The unaffected mixed pair has no gap extension.
Hence all three local pairs have disjoint interiors.

This proof also retains Section 5's stronger boundary fact: the closed
flank petal misses the closed opposite slit segment. Both w and b have
strictly negative determinants against the same separator, even when
B=kappa_w or (T) is equality. This fact prevents a pinched auxiliary
hexagon in the high-curvature argument below.

## 2. The all-low source alternative

Every vertex curvature is at most pi, and Section 1 gives the three local
pairs at the actual slit c. Apply
[LOW_CURVATURE_FAR_REDUCTION.md](LOW_CURVATURE_FAR_REDUCTION.md): the equal
cut lengths exclude both finite entries, and the face-curvature bound
excludes the opposite petals. All six far pairs are safe. Together with
the 19 shared-vertex pairs and three local pairs, this covers all 28.

## 3. The source-at-least-pi alternative

The pole-angle proof needs no ranking to exclude a finite-cut entry once
the local pairs are safe. The spherical link at v makes every angle(w,v,a)
strictly less than pi/2. The neighboring flattened apex must therefore lie
outside the triangle in which a supposed entry would trap it. Apply this
argument at both sides of the same slit.

For the opposite petals, Case A's no-wrap bound is immediate from
Gamma_v=2*pi-kappa_v<=pi. The base-cone branch has no ranking hypothesis.
In the remaining small-fan branch, the closed-curve argument would require

    nu_m > kappa_a+kappa_c+kappa_w.

Its containment uses the local pairs supplied in Section 1. Its auxiliary
region is simple, including boundary cases, by the strict local boundary
fact just proved. The convex-vertex cone bound and (T) give

    kappa_c+kappa_w-nu_m
      >= (pi-kappa_w)/2+kappa_w-(pi-kappa_v/2)
       = (kappa_v+kappa_w-pi)/2 > 0.

The last inequality is strict even when kappa_v=pi, since kappa_w>0.
This contradicts the angle requirement. Both opposite-petal pairs are
safe; the retained boundary-entry and interior-hinge arguments now give
the other far pairs. No use of R remains.

## What has been reduced, and what has not

For the original Lemma F under H, a counterexample must have

    2*kappa_c+kappa_w < pi.

In particular kappa_w<pi, and c is a low-curvature equator vertex. In the
all-low branch, it must additionally have a local overlap by the previous
conditional theorem. The exact local-failure example satisfies this strict
threshold failure and has two local overlaps, but **all its far pairs are
safe**. Thus the remaining branch is nonempty without refuting Lemma F.

The threshold is sufficient, not necessary. A net can still work when it
fails (T). A rejected or unresolved threshold check must not be described
as an overlap. The selected 28/28 count and the 5/7 whole-type count stay
unchanged; this extends the set of individually proved slit choices.
