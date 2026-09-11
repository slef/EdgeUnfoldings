# Equal cut-edge lengths close the low-curvature branch

11 September 2026. **Complete written proof of the selected-net theorem.**
The dependency audit is included below; independent mathematical review
and formal verification have not been performed.
No numerical experiment is a premise. The argument below addresses the
maximum-curvature slit R; it does not assert the every-slit Lemma F.

## Selected-net theorem

Choose a maximum-curvature vertex v of a strictly convex octahedron (H).
Let w be its opposite vertex. Choose a maximum-curvature equator vertex
c=u_k (R). Cut the four original edges at v and the original edge wc.
Then this selected net is nonoverlapping: distinct face interiors are disjoint.
Every cut is an original edge. Ties in either selection are allowed.

The branch kappa_v>=pi was proved in [LEMMA_F_POLE_ANGLE.md](LEMMA_F_POLE_ANGLE.md).
This note supplies a different contradiction for kappa_v<=pi. Thus the
two branches cover every source curvature, with their common boundary.

## 1. Recall exactly what a finite-cut crossing would imply

Consider the last cut copy, wb. Put i=k+1, m=k, a=u_i, and let c be the
first copy of the same physical slit vertex b. Let P be the developed
apex of V_i and M the developed apex of the neighboring V_m.

By the through-fan part of Lemma L, a hypothetical intersection of
int(V_i) with the open finite segment wb must approach across the gap.
The patch Q_i is reflex at a. Put

```
theta = the corner of Q_m at a,
kappa = kappa_a,
delta = omega_m+kappa_w,
s = |aP| = |aM| = |av|,
r = |aw|.
```

The vertex-angle identity gives theta+angle_a(Q_i)=2*pi-kappa, so
0<theta<pi and 0<theta+kappa<pi. At the common uncut copy of a, the
two boundary edges aM and aP are separated by exactly the curvature gap
kappa. The order on the side containing Q_m and the cut gap is

```
aw, ac, aM, aP.
```

The cut ray first enters V_i across the open edge aP, at q, and q is
before b. In particular 0<|aq|<s. Choose p just beyond q, inside V_i and
before b, still with |ap|<s. The containment proof in Section 1 of
LEMMA_F_POLE_ANGLE.md gives

```
Q_m is contained in triangle T=conv{w,a,p}.
```

That proof uses only shared-vertex separation and the local Lemma L.
For completeness: W_m cannot cross ap (inside V_i), wa (its boundary),
or wp (outside its angular wedge). Its open edge ac is inside T.
The attached V_m cannot cross ap (shared vertex a), wp (a subsegment of
wb, on the boundary of the local target W_(k+3)), or wa (its corner
theta<pi puts the entire patch on the W_m side). Generic interior paths
exclude escape through a vertex. Closed containment allows tangencies.
Thus M is in T and on the same closed side of line wq as a.

## 2. An elementary equal-radius lemma

Use coordinates a=(0,0), w=(r,0), and orient the plane so that

```
M = s*(cos(theta), sin(theta)),
P = s*(cos(theta+kappa), sin(theta+kappa)).
```

The triangle awq has angles theta+kappa at a and delta at w. Therefore

```
0 < theta+delta < theta+kappa+delta < pi.             (1)
```

An oriented direction along wq is d=(-cos(delta),sin(delta)). Because
q=t*P with 0<t<1, its collinearity with w gives

```
r*sin(delta) = t*s*sin(theta+kappa+delta)
            <   s*sin(theta+kappa+delta).            (2)
```

Closed containment puts M on a's side of this line. Its determinant is

```
det(d,M-w) = r*sin(delta)-s*sin(theta+delta) >= 0.    (3)
```

Combining (2) and (3) and dividing by s>0 yields

```
sin(theta+kappa+delta) > sin(theta+delta).
```

The sine-difference formula and (1) now give

```
2*sin(kappa/2)*cos(theta+delta+kappa/2) > 0,
2*theta + 2*delta + kappa_a < pi.                    (4)
```

Here sin(kappa/2)>0, and the cosine's argument lies strictly in (0,pi).
There is no unaccounted turn or monotonicity assumption. The strict
inequality comes from q being strictly inside aP. M is allowed to lie
on line wq, so this reasoning does not require a strict clearance from
the local Lemma L.

This is the new point: the equal lengths of the two copies of av couple
the neighboring patch to the petal that was supposed to cross the cut.
An obtuse angle at M no longer defeats the argument.

## 3. The neighboring blue face gives the opposite inequality

In triangle W_m=wca, write eta=angle_a(W_m), gamma=angle_c(W_m), and
mu=angle_a(V_m)>0. Then theta=eta+mu, and the triangle angle sum gives

```
theta+delta = eta+mu+omega_m+kappa_w
            = pi-gamma+mu+kappa_w.
```

The convex-vertex cone inequality at c gives
gamma<=pi-kappa_c/2. Consequently

```
2*theta+2*delta+kappa_a
  >= kappa_a+kappa_c+2*kappa_w+2*mu.                 (5)
```

Together, (4) and (5) prove the following necessary condition for a
finite-cut crossing:

```
kappa_a+kappa_c+2*kappa_w+2*angle_a(V_m) < pi.        (6)
```

Thus kappa_a+kappa_c+2*kappa_w>=pi alone is a sufficient exclusion,
whenever the stated through-fan and local nonoverlap premises hold.

## 4. Why low maximum curvature makes a crossing impossible

Under H and kappa_v<=pi, every vertex curvature is at most pi.
The three vertices complementary to the blue face {w,c,a} therefore
have total curvature at most 3*pi. Subtract from Gauss--Bonnet:

```
kappa_w+kappa_c+kappa_a >= 4*pi-3*pi = pi.
```

Since kappa_w>0 and mu>0, (5) is strictly greater than pi, contradicting
(4). This excludes the last finite-cut crossing. Reflecting the net gives
the first-cut exclusion at the same physical slit and under the same
hypotheses.

An explicit sum of nonnegative terms makes the contradiction auditable.
Let {v,d,e} be the three vertices outside the face {w,c,a}. The exact
angle and curvature identities above yield

```
2*theta+2*delta+kappa_a-pi
  = (pi-kappa_v)+(pi-kappa_d)+(pi-kappa_e)
    + kappa_w + 2*mu + (2*pi-kappa_c-2*gamma) > 0.
```

The first three terms are nonnegative in this branch, the final term is
nonnegative by the cone inequality, and kappa_w and mu are positive.
This directly contradicts (4); no search or limiting argument is needed.

Both finite-cut conditions of [LEMMA_F_CUT_RAYS.md](LEMMA_F_CUT_RAYS.md)
now hold. Its reduction supplies all six far pairs, while Lemma L and
shared-vertex separation supply the other 22.

## 5. Scope

Combining the two source-curvature branches proves the selected rule
for every strictly convex octahedron. It settles the octahedral
six-vertex type, including the previously remaining common-direction
three-patch pattern. It does not prove that all four slits are safe,
and it does not automatically settle either nonsimplicial type: avoiding
artificial diagonals in limits remains necessary.

The audit below checks the finite-cut containment, curvature-gap orientation,
and whole-net reduction, including boundary contacts. The Case A no-wrap and
apex-cone argument and the Case B base-cone partition retain their stated
hypotheses. Exact tests of explicit examples validate the implementation and
may catch mistakes; they do not prove the theorem. The proof is a research
manuscript, not a machine-checked derivation or an independently reviewed result.

Run `python3 -m n6.selected_octahedron_examples` for nine independent
coordinate-domain replays. They include a point with source curvature
exactly pi, a full 18-coordinate box crossing that threshold, and the regular
octahedron with tied selections. The hypothesis checker deliberately accepts
an unresolved comparison with pi: both sides and equality have written proofs.
Each saved domain also has an independent all-28-pair certificate.

## Dependency audit: the six far pairs really follow

The through-fan use of L does not move the chosen slit or assume R at a
different vertex: only the patch angles are reindexed in an inequality
that holds at every opening under the pole comparison. The finite-cut
containment uses the actual selected net and the local V_m/W_(k+3)
theorem at that same slit.

For opposite petals, the existing exhaustive partition has three branches:

* Case A, kappa_u+kappa_u'<nu_j. The base-ray angles alpha,beta are
  positive with alpha+beta<pi. Under H, writing G=2*pi-kappa_v, the
  bound kappa_u+kappa_u'>=4*G-4*pi shows
  nu_i+nu_j<=pi+kappa_u+kappa_u' (trivial if G<pi). The same holds
  on the other side. These are precisely the apex-cone no-wrap bounds.
  The two apex cones can intersect only if both cut edges reach the
  intersection of their lines. That would trap the middle apex inside
  triangle uu'p while making its sum of distances to u,u' greater than
  the available two cut-edge lengths. Convexity of that distance sum
  gives the strict contradiction. Thus Case A is safe independently
  of the finite-cut tests.
* Base-cone branch, alpha+beta>=pi and sigma+tau>=pi. The left cone
  and the reversed right cone lie in a convex sector of width at most
  pi that excludes the positive base direction. Their difference cannot
  equal the nonzero base vector. Equalities are included; H is not used.
* Small-fan branch, sigma+tau<pi. The finite-cut test and L make the
  quadrilateral a,p,b,w simple for p inside a supposed opposite-petal
  overlap. Its interior at w faces the fourth patch: the other choice
  would trap the middle orange triangle above its base in a region
  whose entire boundary is below that base. Shared vertices and L then
  trap the fourth patch. Removing it leaves the six-sided region of
  LEMMA_F_CUT_REDUCTION.md. Its angle sum requires
  nu_m>kappa_a+kappa_c+kappa_w, whereas R and the source cone bound
  give kappa_c+kappa_w-nu_m>0.

The six-sided region needs particular care at contacts. Its inserted
slit copy c is strictly inside the quadrilateral: it cannot lie on ap
or bp because those open segments are inside the two petals it avoids,
and its radial direction differs from both boundary radial directions.
The inserted apex M cannot lie on ap or bp for the same reason. It cannot
lie on the opposite finite slit edge by the strict local boundary result
in Section 5 of LEMMA_L_PROOF.md. Nor can it lie on segment wa: its
direction from a differs from aw by the positive patch corner, strictly
below 2*pi; a straight corner points away from w. M is not w because
the two faces of its patch are on opposite sides of their common edge.
The only shared boundary of the fourth patch and the quadrilateral is
wa. The positive curvature gap at a and the positive slit gap at w
leave positive angles in the remaining region. Hence the six-sided
region is simple and its angle sum is legitimate, including the original
solid's other equality cases.

After opposite-petal safety, each distant petal has all three open edges
of its cut-side blue target excluded: the finite slit edge by the new
theorem, the other radial edge by shared-vertex separation, and the
equator edge by opposite-petal separation. A path inside the convex
petal cannot enter the target without crossing one of those edges.
The two interior-fan targets follow by the same boundary argument and
the interior-hinge lemma, which correctly includes its two local-pair
exceptions. This uses the surviving direction of HINGE_AUDIT.md, not
the refuted implication at a cut boundary.

All these statements exclude positive-area overlap. The strict local
boundary result above is used only where simplicity of the auxiliary
six-sided region needs it. No general-position assumption on the solid,
unique sharpest vertex, or unique maximum-curvature slit is required.
