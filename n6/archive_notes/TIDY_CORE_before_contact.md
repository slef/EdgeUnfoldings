# Preserved interior-point version of the geometric core

This is the complete earlier draft, before the first-contact shortening.
The original research proofs are also retained.

# Shared geometric core — streamlined proof draft

12 September 2026. A separate exposition developed during the proof review.
The original proofs and alternatives remain unchanged. This draft is being
self-audited; independent mathematical review is still pending.

## Setting and the two outputs

Triangulate the convex six-vertex surface as an octahedron. Write v,w for
opposite poles and u_0,...,u_3 for the cyclic equator. The fan faces are
W_i=w u_i u_(i+1), their petals V_i=v u_i u_(i+1), and their unions Q_i.
Cut the four edges at v and wu_0. The blue fan opens in order W_0,...,W_3;
u_0 has first and last copies c,b, and each petal has its own apex copy.
Curvature kappa_x is 2*pi minus the face-angle sum at x. Every vertex is
genuine, so 0<kappa_x<2*pi, and the six curvatures sum to 4*pi.

Two consequences of the argument will be used:

* **Selected rule.** If (kappa_v>=pi or all six curvatures<=pi) and
  2*kappa_c+kappa_w>=pi, the whole net has disjoint face interiors.
* **Cofacial gate.** If kappa_w<=pi and kappa_c+kappa_w>=pi, all the
  same steps hold except the Case A angle bounds. Proving the two
  opposite-petal pairs in that branch therefore finishes the whole net.

Flat auxiliary hinges are permitted, but triangles are nondegenerate and
the original vertices remain genuine. If the five cuts are original edges,
the uncut auxiliary hinges rejoin whole original faces at the end.
The two conclusions concern this one cut tree, not a mixture of trees.

## Shared-vertex separation

Faces whose unique uncut adjacency path consists entirely of faces incident
to one vertex develop into distinct successive angular sectors there.
Their total angle is at most 2*pi-kappa<2*pi, so their interiors are
disjoint. This also applies to convex polygonal faces, each of which lies
in its corner sector. A boundary point of a nondegenerate safe face cannot
lie in the other's interior: a small disk would give interior overlap.

This observation settles 19 of the 28 triangular face pairs. The remaining
pairs are the three local pairs V_0/V_3, V_0/W_3, V_3/W_0; the opposite
petals V_0/V_2, V_1/V_3; and V_0/W_2, V_1/W_3, V_2/W_0, V_3/W_1.
The displayed groups are disjoint (3+2+4=9).

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

## A single slit-edge separator proves the local lemma

Assume the half-fan hypothesis and 2*kappa_c+kappa_w>=pi. The preceding
bound excludes meeting through the fan. Across its gap, at most one flank
patch is reflex at the slit: the two corners there sum to 2*pi-kappa_c.
Reflect so that Q_0 is the extending patch, with corner pi+rho at c and
extension B at w. Its outer triangle and the positive opposite corner give

    0 < B < rho < pi-kappa_c.

If B<kappa_w the angular ranges are strictly separated across the gap.
Otherwise rho>B>=kappa_w; in particular kappa_c+kappa_w<pi. Put

    w=(0,0), c=(r,0), b=r*(cos(kappa_w),-sin(kappa_w)),
    d=(cos(rho),-sin(rho)),

where d points along the cut edge from c to the first petal apex. That
petal lies on the left of this oriented edge. The threshold gives
0<rho-kappa_w/2<pi/2, and hence

    det(d,b-c)=-2*r*sin(kappa_w/2)*cos(rho-kappa_w/2)<0.

The opposite patch's directions at b, measured relative to d, range from
rho-pi-kappa_w to -(kappa_c+kappa_w), strictly inside (-pi,0).
It therefore lies strictly on the right of the same line. This separates
V_0 from W_3 and V_3. The other mixed pair has no gap extension. All
three local pairs are safe.

We also need a boundary fact: the **closed** V_0 misses the **closed**
opposite slit segment wb. Through the fan, the half-fan bound is strict;
across the gap B<kappa_w is strict. In the remaining case above,
det(d,w-c)=-r*sin(rho)<0 and det(d,b-c)<0, so the entire closed segment
lies strictly on the opposite side of the separator. Reflection gives
the analogous fact for V_3. Equality in the threshold and B=kappa_w
are included; no general-position assumption on the solid is used.

## The finite-entry obstruction in one lemma

Use an octahedrally triangulated convex surface with genuine vertices and
nondegenerate triangles. Flat auxiliary hinges are allowed. Cut the four
edges at source v and one edge at opposite pole w. Suppose the local pairs
are safe and the through-fan route to the relevant cut copy is excluded.

If a remote petal enters the open finite cut segment, let a be its reflex
equator endpoint, c the first slit copy, b the last slit copy, P its apex,
and M the neighboring petal's apex. Set

    r=|aw|, s=|av|=|aP|=|aM|, D=|wv|,
    theta=angle(waM), delta=angle(awb)=omega_m+kappa_w,
    mu=angle(caM), gamma=angle(wca).

Here delta denotes the smaller angle at w in the triangle below; it is
positive and less than pi. All quantities refer to this same unfolding.
We treat entry by V_1 into the last cut segment wb; then a=u_1, m=0,
and c is its first slit copy. Reflection gives the other target. The
through-fan bound forces entry across the gap, with Q_1 reflex at a.
The reflex vertex lies inside Q_1's outer triangle; subdividing there
shows that the ray first enters V_1 across the open edge aP, at q before b.
Choose p just beyond q, inside V_1 and before b, with |ap|<s.
The triangle T=conv{a,w,p} has the short sector omega_m+kappa_w at w.

Here is the full containment argument. W_m starts inside T near w. It
cannot cross ap (whose open points lie inside V_1, a shared-vertex-safe
face), wa (its own boundary), or wp (outside its angular wedge). Its
open edge ac is therefore inside T. The attached V_m starts inside T
along that edge. It cannot cross ap by shared-vertex separation, or wp
by the local V_m/W_3 theorem, since wp is within the slit segment wb.
Its corner theta at a is below pi: theta+angle_a(Q_1)=2*pi-kappa_a
and the second corner is reflex. Thus the whole Q_m is on W_m's side
of line wa, and V_m cannot cross that side either. Convex interior paths
exclude escape through a vertex of T. Consequently

    M in triangle(a,w,p),   M != w.                         (C)

The second assertion holds because M and w lie on opposite sides of ac.
This uses only the local and shared-vertex facts already proved, with no
opposite-petal or distant-fan premise. Tangencies are allowed in (C).

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

## Opposite petals: an exhaustive three-part partition

Take three successive patches with middle base u=(0,0), u'=(ell,0),
middle petal apex M above that base, and middle fan face below it.
Write phi,psi,nu for the middle petal's angles; lambda,rho for the outer
petals' apex angles; K=kappa_u+kappa_u'; and

    alpha=phi+kappa_u, beta=psi+kappa_u', theta=alpha+beta=pi-nu+K.

Let sigma,tau be the sums of the two fan-face angles at u,u', and a_0,b_0
the outer petals' angles at these base endpoints. The vertex sums are

    alpha+sigma+a_0=2*pi, beta+tau+b_0=2*pi.

In particular theta+sigma+tau>2*pi. Exactly one of the following applies:
theta<pi (Case A); theta>=pi and sigma+tau>=pi (base cones); or
sigma+tau<pi (the small-fan pocket). Equalities belong to the middle case.

**Case A.** The rays of the two copied cut edges have directions alpha
from u and pi-beta from u'. They meet at p*. The middle apex M is strictly
inside triangle uu'p*, since phi<alpha and psi<beta. Put

    s=|uM|=|uP|, s'=|u'M|=|u'Q|, L=|up*|, R=|u'p*|.

Convexity of x -> |ux|+|u'x|, with value ell at the base endpoints and
strictly larger value L+R at p*, gives s+s'<L+R. Hence the two cut edges
cannot both reach p*.

If lambda,rho<=theta, the left apex cone and the reversed right apex
cone lie in the sector S=[pi-beta,pi+alpha], of width theta<pi. With e,f
the unit vectors at its last and first boundaries, the sine rule gives

    Q-P=(s-L)*e+(s'-R)*f.

Intersection of the translated cones would put Q-P in S, requiring both
coefficients nonnegative. This contradicts the strict distance-sum bound.

For the selected rule, these angle bounds are automatic. If kappa_v>=pi,
the whole apex-angle sum Gamma_v<=pi. In the all-low alternative,
Gauss--Bonnet on the three vertices outside {v,u,u'} gives
K>=pi-kappa_v. In either case Gamma_v<=pi+K, so
lambda+nu,rho+nu<=pi+K, which is precisely lambda,rho<=theta.
For the cofacial gate these bounds must be supplied separately, or replaced
by another valid Case A separator.

**Base cones.** The left base cone and the reversed right base cone have
direction intervals [alpha,2*pi-sigma] and [tau,2*pi-beta]. Both lie in

    S=[min(alpha,tau), 2*pi-min(sigma,beta)].

The sums alpha+sigma and beta+tau exceed pi. With theta>=pi and
sigma+tau>=pi this sector has width at most pi and excludes the positive
base direction. A meeting would require the base vector u'-u to be the
difference of vectors in the two original cones, hence to belong to S.
This is impossible, including equality in either threshold.

**Small-fan pocket.** Treat the last triple Q_1,Q_2,Q_3; reflection treats
the first. Put a=u_1, u=u_2, u'=u_3, b=the last slit copy, c=the first,
and let P_1,P_3,M_0 be the corresponding petal apices. Suppose p is inside
both V_1 and V_3. Choose it off the finitely many lines needed below.
The two outer base rays are

    u -> a: (cos(sigma),-sin(sigma)),
    u' -> b: (-cos(tau),-sin(tau)).

Each petal is across its own equator line from w. Thus p=(x,y) satisfies

    sin(sigma)*x+cos(sigma)*y<0,
    sin(tau)*(x-ell)-cos(tau)*y>0.

Elimination of x gives

    y < -ell*sin(sigma)*sin(tau)/sin(sigma+tau) < 0.

The points a,b,w also lie strictly below uu'. The curve
Gamma=a,p,b,w,a is simple: ap is inside V_1 and cannot meet wb by the
finite-cut result; bp is inside V_3 and cannot meet wa by local V_3/W_0
separation. The same facts exclude the other endpoints; generic p avoids
the remaining collinearities. Its closed interior D lies strictly below
uu'. At w this interior cannot contain the sector occupied by W_1,W_2,W_3:
that would trap W_2 itself, whose interior cannot cross ap or bp by
shared-vertex separation, or the two radial sides by fan sectors. But its
base vertices u,u' are on uu', outside D. Therefore D contains the other
sector at w, occupied by W_0 and the slit gap.

The entire Q_0 is in D. Against ap, W_0 and V_0 are protected by their
shared uncut a; against bp, both are protected by the local lemma.
W_0 cannot cross a radial side. V_0 cannot cross wb by the strict local
boundary fact, or wa by shared-vertex separation from W_1. Both faces
have interior points in D, starting near w and then along their hinge.
Generic interior paths justify containment despite possible tangencies.

Q_0 meets Gamma only along wa. Indeed c cannot lie on ap or bp by the
same safe-face facts and has a different radial direction from either
side. M_0 cannot lie on ap or bp either, or on wb by strict local
separation. It cannot lie on wa: its positive corner at a is below 2*pi;
if that corner is straight, its ray points away from w. Also M_0!=w,
as they lie on opposite sides of ac. Removing Q_0 from D therefore gives
the simple hexagon a,p,b,w,c,M_0,a.

Let gamma_p>0 be its angle at p, delta_a=angle(p,a,P_1)>=0 and
delta_b=angle(p,b,P_3)>=0. Its angles, in boundary order, are

    kappa_a+delta_a, gamma_p,
    2*pi-angle_b(W_3)-angle(p,b,u'), kappa_w,
    2*pi-angle_c(W_0)-angle_c(V_0), 2*pi-nu_0.

The complementary angle at b is determined, not chosen: orient the fan
counterclockwise from wc to wb. Since D contains the other sector at w,
Gamma runs clockwise and D is on the right of b->w. W_3 is on the left
of that directed edge. Thus D's angle at b is the complement of the
W_3 corner plus the part of V_3 between bu' and bp. At a, removing Q_0
leaves the curvature gap followed by delta_a. At c and M_0 it leaves
the complements of the removed patch corners, as listed.

Their sum is 4*pi. Using the full face-angle sum at the physical slit
vertex and angle_b(V_3)=angle(p,b,u')+delta_b yields

    nu_0=kappa_a+kappa_c+kappa_w+gamma_p+delta_a+delta_b
        >kappa_a+kappa_c+kappa_w.                       (P)

For the selected rule, 2*kappa_c+kappa_w>=pi implies
kappa_c+kappa_w>pi/2. Thus (P) forces nu_0>pi/2 and the link bound
forces kappa_v<pi. The source condition now forces all six curvatures
to be at most pi. Gauss--Bonnet gives kappa_a+kappa_c+kappa_w>=pi,
contradicting (P), since nu_0<pi. For the cofacial gate,
kappa_c+kappa_w>=pi contradicts (P) immediately. This single argument
replaces the original separate high- and low-source pocket estimates.

Both opposite-petal pairs are now safe, provided the needed Case A bounds
were supplied. The actual slit was never moved in this proof.

## Four boundary checks finish the net

The following table lists each remaining petal/fan pair. Every open edge
of its fan target is either a proved-safe finite slit segment or borders
one of the already safe faces shown in the last column.

| Pair | Finite slit edge, if any | Faces across the other target edges |
| --- | --- | --- |
| V_1 / W_3 | wb | W_2 (shared vertex), V_3 (opposite petals) |
| V_2 / W_0 | wc | W_1 (shared vertex), V_0 (opposite petals) |
| V_0 / W_2 | none | W_1 (shared vertex), W_3 (local), V_2 (opposite petals) |
| V_3 / W_1 | none | W_0 (local), W_2 (shared vertex), V_1 (opposite petals) |

An interior point of a petal on any such open edge would create overlap
with its already-safe neighbor. Each petal has interior points outside
its target, near its own equator midpoint and within its own fan wedge.
If it also had an interior point inside the target, a generic path within
the convex petal would cross an open target edge. Every crossing has been
excluded. This settles the final four pairs directly; no separate hinge
reduction is needed. It proves both outputs stated at the beginning.

If auxiliary diagonals were added, they remained uncut. Their adjacent
triangles rejoin the original convex facets. A positive-area overlap of
two facets would contain a point away from the finitely many diagonals,
giving an already-excluded triangle-interior overlap. Thus the result is
an original-edge unfolding whenever the five cuts were original edges.

## A wider Case A separator for the prism switches

The Case A proof also applies to convex polygonal outer faces contained in
their full apex cones. Retain its notation, and assume
lambda+rho<pi+theta. Then either of the following suffices:

    s<=L and lambda<=(pi+theta)/2;
    s'<=R and rho<=(pi+theta)/2.                         (W)

For the left condition with lambda<=theta, take the linear functional
giving the coefficient of e in the basis e,f. It is nonnegative on both
the left cone and the reversed right cone (the latter has width rho<pi).
Its value on Q-P is s-L<=0, so the two faces lie on opposite sides of a
line. The common line at equality cannot contain face interiors.

For theta<lambda<=(pi+theta)/2 put g at direction pi+alpha-lambda.
Both cones lie counterclockwise of g in a sector of width
lambda+max(rho-theta,0)<pi. Set A=L-s>=0 and B=s'-R<A. Then

    det(g,Q-P)=-A*sin(lambda)+B*sin(lambda-theta)<0.

If B<=0 strictness is immediate; if B>0, use B<A and
sin(lambda)>=sin(lambda-theta), which follows from (W). This strictly
separates the translated cones. Reflection proves the other condition.

Thus **both outer angles at most (pi+theta)/2 suffice**, since at least
one cut side is short. **A nonobtuse middle angle also suffices.** To see
this, write M=a*u+b*u'+t*p* with a,b,t>0 and a+b+t=1. Then
p*-M=(a/t)*(M-u)+(b/t)*(M-u'). If nu<=pi/2 the dot product of M-u and
M-u' is nonnegative, so expansion of squared lengths gives both L>s
and R>s'. The angle-sum premise ensures at least one of lambda,rho is
below (pi+theta)/2, and that side satisfies (W).

The angle-sum premise is automatic whenever lambda,rho and nu are
original angles at one source: lambda+rho+nu<=Gamma_v=2*pi-kappa_v,
whereas pi+theta=2*pi-nu+K and kappa_v+K>0. This includes the two
quadrilaterals in the prism fallback and the cofacial near-star candidates.

## Audit boundary

This is a complete reconstructed exposition of the shared geometric core,
still under self-audit. The exact checks in tidy_audit.py check identities
and specified coordinate domains, not this universal geometric argument.
The original longer proofs, failed reductions and alternative estimates
remain available. Independent mathematical review is still needed.
