# Shared geometric core — streamlined proof draft

12 September 2026. A separate exposition developed during the proof review.
The original proofs and alternatives remain unchanged. This draft is being
self-audited; independent mathematical review is still pending.

## Closed-link bound and a half-fan lemma

At a genuine vertex p, its tangent cone cuts the unit sphere in a convex
spherical polygon K of positive area in an open hemisphere. Its perimeter
is Gamma_p=2*pi-kappa_p. Flat auxiliary hinges only subdivide its sides.
If a is an edge direction and q any direction in the closed polygon K,

    2*distance(a,q) < Gamma_p.                         (L)

Indeed, extend the shortest arc from a through q to a boundary point c.
The two boundary paths from a to c are each at least distance(a,c), and
cannot both coincide with that shortest arc without giving K zero area.
Their sum is therefore strictly greater than 2*distance(a,c), which is
at least 2*distance(a,q). The case q=a is immediate. In particular every
original or subdivided face angle is strictly below Gamma_p/2.

**Half-fan lemma.** If kappa_v>=pi or kappa_w<=pi, every flattened patch
formed by one fan triangle at w and its attached petal at v has angular
span strictly below Gamma_w/2, as viewed from w.

A convex patch has span equal to its fan angle, so (L) suffices. Otherwise
the patch has one reflex equator corner and is contained in the triangle
w,u,P at the other equator endpoint u and the developed petal apex P.
Write r=|wu|, s=|vu|, D=|wv|, t=|wP|, alpha=angle(uwv),
beta=angle(uvw), and gamma=angle(uwP), the patch's whole angular span.
Its corner at u is below pi. The spherical triangle inequality and the
cosine law give t>=D. If beta<=pi/2, then

    cos(gamma)-cos(alpha)
      = (t-D)*(t*D-r*r+s*s)/(2*r*t*D) >= 0,

so gamma<=alpha<Gamma_w/2 by (L). If beta>pi/2, then r>s and
cos(gamma)=(r*r+t*t-s*s)/(2*r*t)>0, hence gamma<pi/2. This second case
forces kappa_v<pi by (L) at v, so the hypothesis supplies kappa_w<=pi
and Gamma_w>=pi. Again gamma<Gamma_w/2. Straight patch corners follow
by the same containment or the convex angular sector. No strict
dihedral angle at an auxiliary hinge is required.

For first and last patches of any opening, their two angular spans sum
to less than Gamma_w. In particular their extensions toward the interior
of the fan cannot bridge the intervening fan angles. This proves the
through-fan part of Lemma L at every opening, without a slit ranking or
the separate one-sided spherical-link estimate of the original proof.

It also excludes a remote petal reaching a finite slit copy through the
fan: apply this inequality to the same two physical patches in the
opening where they are first and last. Their angle data do not change.
The actual cut tree is not changed, and no slit-selection premise is
reused at a different vertex.

## The finite-entry obstruction in one lemma

Use an octahedrally triangulated convex surface with genuine vertices and
nondegenerate triangles. Flat auxiliary hinges are allowed. Cut the four
edges at source v and one edge at opposite pole w. Suppose the local pairs
are safe and the through-fan route to the relevant cut copy is excluded.

If a remote petal enters the open finite cut segment, let a be its reflex
equator endpoint, c the first slit copy, b the last slit copy, P its apex,
and M the neighboring petal's apex. Set

    r=|aw|, s=|av|=|aP|=|aM|, D=|wv|,
    theta=angle(waM), delta=angle(aw,bw)=omega_m+kappa_w,
    mu=angle(caM), gamma=angle(wca).

Here delta denotes the smaller angle at w in the triangle below; it is
positive and less than pi. All quantities refer to this same unfolding.
The local and shared-vertex barriers give a point p in the entering petal
with |ap|<s and the closed containment

    M in triangle(a,w,p),   M != w.                         (C)

The detailed barrier proof is retained in LEMMA_F_POLE_ANGLE.md, Section 1.
It uses no opposite-petal or far-fan conclusion. A fresh complete account
will precede this lemma in the final streamlined presentation.

**Lemma.** Such an entry forces both

    kappa_v < pi,                                         (E1)
    kappa_a+kappa_c+2*kappa_w+2*mu < pi.                   (E2)

**Proof of (E1).** Put a=0 and e=M/s. The linear functional e dot x
takes value s at M, value 0 at a, and a value strictly below s at p.
Containment (C), with M different from w, therefore requires e dot w>s.
Writing t=|wM| gives

    r^2 > s^2+t^2.

The neighboring patch angle at a is below pi: it is the complement of
the entering patch's reflex corner, minus the positive curvature at a.
The spherical triangle inequality at a, followed by the cosine law, gives
t>=D. Consequently r^2>s^2+D^2, so the original angle beta=angle(wva)
is obtuse. The closed spherical-link bound gives

    2*beta < 2*pi-kappa_v,

and hence kappa_v<pi.

**Proof of (E2).** The first crossing q of the cut ray is strictly inside
the edge aP, so q=lambda*P with 0<lambda<1. Orient coordinates by

    a=0, w=(r,0),
    M=s*(cos(theta),sin(theta)),
    P=s*(cos(theta+kappa_a),sin(theta+kappa_a)).

The triangle awq has angle delta at w, so
0<theta+delta<theta+kappa_a+delta<pi. The cut line, oriented by
d=(-cos(delta),sin(delta)), yields

    r*sin(delta)=lambda*s*sin(theta+kappa_a+delta),
    r*sin(delta)-s*sin(theta+delta)>=0.

The second inequality is exactly (C)'s half-plane containment. Thus
sin(theta+kappa_a+delta)>sin(theta+delta). The sine-difference identity,
with both arguments in the stated interval, gives

    2*theta+2*delta+kappa_a < pi.

But theta+delta=pi-gamma+mu+kappa_w, and the face-angle link bound gives
2*gamma<=2*pi-kappa_c. Therefore

    2*theta+2*delta+kappa_a
      >= kappa_a+kappa_c+2*kappa_w+2*mu.

This proves (E2). Both strict conclusions tolerate tangency in (C): the
strictness comes from |ap|<s and lambda<1, not from generic position of
the original solid.

## One contradiction replaces the two source-curvature cases

Assume either kappa_v>=pi or every vertex curvature is at most pi.
A finite entry would first force kappa_v<pi by (E1), so the source
assumption now forces every curvature to be at most pi. The three vertices
outside the blue face wca then have total curvature at most 3*pi.
Gauss--Bonnet gives kappa_w+kappa_c+kappa_a>=pi, contradicting (E2).

Thus both finite cut segments are safe, by reflection. This is the same
geometric content as the original projection and equal-radius proofs,
combined into a single contradiction. It retains the weaker source-choice
theorem, including source curvature equal to pi and all-low equalities.

For the more general cofacial curvature gate, the source assumption is
unnecessary: the finite-cut budget kappa_a+kappa_c+2*kappa_w>=pi
already contradicts (E2). This will supply the same lemma in the two
nonsimplicial proofs without silently imposing a sharpest source.

## Review work still to integrate

The local separator and closed-link bounds, the Case A cone proof, the
small-fan closed curve, and the original-face recovery are not replaced by
the lemma above. They remain explicit dependencies until their full short
proofs have been integrated into this document. No new whole-type status
is inferred from this partial exposition.
