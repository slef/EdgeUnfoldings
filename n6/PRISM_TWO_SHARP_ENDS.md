# The two-pair prism net works when both end vertices are sharp

12 September 2026. A written geometric proof, pending independent review.
No numerical experiment is a premise. This proves a complete curvature
branch of the prism-with-one-diagonal type, not the entire type.

## Statement and original faces

Use the original face labels

    A = triangle 021       B = quadrilateral 0352
    C = triangle 013       D = quadrilateral 1254
    E = triangle 143       F = triangle 345.

Vertices 2 and 5 are joined by the original edge 25. If

    kappa_2 >= pi and kappa_5 >= pi,

cut the five original edges 02,12,25,35,45. The resulting net has disjoint
face interiors. Equality in either curvature assumption is included.

Its uncut face adjacencies are C-A, C-B, C-E, E-D, E-F. Thus C and E form
the central pair, with two leaves on each. Every face pair except A/F and
B/D has a common uncut vertex along its unique adjacency path. Such pairs
occupy disjoint angular sectors at that vertex, since its total incident
angle is strictly below 2*pi. It remains to separate A from F and B from D.
The two quadrilaterals stay whole; no artificial diagonal is cut or needed.

Write angle(X,p) for the full interior angle of original face X at p.

## Two elementary planar tools

The base-cone proof in CASE_PARTITION.md applies equally to convex polygonal
outer faces. It does not require the intervening face to be a triangle.
Here is the exact version used below.

Put two uncut base vertices u,u' on a horizontal line, with the middle face
above it and the intervening central faces below. Let phi,psi be the middle
face angles at u,u'. Let sigma,tau be the sums of the intervening central
face angles at the two vertices. Let a,b be the outer face angles there.
Assume these lists exhaust the incident faces at each base vertex. Set

    alpha=phi+kappa_u, beta=psi+kappa_u'.

Then alpha+sigma+a=2*pi and beta+tau+b=2*pi. The actual left outer cone has
directions [alpha,2*pi-sigma]; the reversed right outer cone has directions
[tau,2*pi-beta], modulo one turn. Their widths a,b are in (0,pi).
If alpha+beta>=pi and sigma+tau>=pi, they fit in the closed convex sector

    [min(alpha,tau), 2*pi-min(sigma,beta)],

of width at most pi. Its endpoints avoid the positive horizontal direction.
Consequently their vector sum cannot equal u'-u, so the two translated
outer cones are disjoint. This includes equality in both comparisons.
The same proof is unchanged by reflecting the diagram or exchanging sides.

When the middle face is a triangle with apex angle nu and the two outer
faces have copies of that same apex, Case A is alpha+beta<pi. The equal-cut-
length proof in CASE_A_CONES.md separates their apex cones whenever both
outer apex angles are at most alpha+beta. That proof uses only containment
in convex apex cones; it also applies to convex quadrilateral outer faces.

## A face angle at either sharp end is strictly below pi/2

At a genuine vertex, the spherical link is a convex polygon of positive
area. For any link side of length omega, the complementary boundary path
is strictly longer than omega: equality in the spherical triangle inequality
would put the whole boundary on the same shortest arc and give zero area.
Thus 2*omega<Gamma, where Gamma=2*pi-kappa is the incident face-angle sum.
At vertices 2 and 5, Gamma<=pi, so every original face angle is below pi/2.

In particular,

    angle(B,2)+angle(B,5)<pi,
    angle(D,2)+angle(D,5)<pi.                       (1)

This strict conclusion also holds when an end curvature equals pi.

## The triangular caps A and F are separated

First view the two caps around the middle quadrilateral B, whose base is
03. The intervening angles are

    sigma_B = angle(C,0),
    tau_B   = angle(C,3)+angle(E,3).

Because B is a quadrilateral, (1) gives

    angle(B,0)+angle(B,3)
        =2*pi-angle(B,2)-angle(B,5)>pi.

Adding the positive curvatures at 0 and 3 shows alpha_B+beta_B>pi.
The base-cone lemma therefore separates A/F whenever

    S_B = sigma_B+tau_B = pi-angle(C,1)+angle(E,3) >= pi.

Alternatively view the same two caps around D, with base 14. The same
argument using (1) gives alpha_D+beta_D>pi. Here

    S_D = angle(C,1)+angle(E,1)+angle(E,4)
        = pi-angle(E,3)+angle(C,1).

The two quantities satisfy S_B+S_D=2*pi. At least one is at least pi,
and that view supplies the required separator. Hence A/F is safe.

## The quadrilaterals B and D are separated

View them first around the lower cap A, with base 01 and copied apex 2.
The intervening central angle sum is

    T_A = angle(C,0)+angle(C,1)+angle(E,1)
        = pi-angle(C,3)+angle(E,1).

If this view is Case A, put nu=angle(A,2). The full incident sum at 2 is

    nu+angle(B,2)+angle(D,2) = Gamma_2 <= pi.

Each outer apex angle is therefore less than pi-nu, whereas
alpha+beta=pi-nu+kappa_0+kappa_1>pi-nu. Both no-wrap bounds hold strictly,
and the equal-cut-length apex-cone proof separates B/D. If the view is
not Case A, the base-cone proof separates them whenever T_A>=pi.

Now view the same quadrilaterals around the upper cap F, with base 34 and
copied apex 5. The corresponding central angle sum is

    T_F = angle(C,3)+angle(E,3)+angle(E,4)
        = pi-angle(E,1)+angle(C,3).

Exactly the same argument uses Gamma_5<=pi: its Case A is safe, and its
other branch is safe if T_F>=pi. Since T_A+T_F=2*pi, choose a view whose
T is at least pi. That view is safe in either of its exhaustive branches.
Thus B/D is safe, completing every face pair of the net.

## What this changes, and what it does not

The earlier exact counterexample to the unrestricted two-pair tree is
compatible with this theorem: it does not have both end curvatures at least
pi. The proof supplies a simple original-edge rule for this entire branch.
It does not certify other high-curvature prism shapes or the minus-edge type.

The weaker hypothesis that only one end is sharp is insufficient. The
exact rational witness prism-one-sharp-failure.certificate.json has
kappa_5>pi and kappa_2<pi, but B/D have certified positive-area overlap.
A same-coordinate repair uses star(3) plus 25; the old high-source theorem
and a separate all-pairs certificate both verify that repair. The report
prism-one-sharp.verification.json records the original facets, curvature
bands, overlap, and repair. This negative result is independent of the
universal proof above.

In the proposed broader strategy, this handles precisely the prism branch
where both possible fan vertices 2 and 5 are sharp. The separate proposed
sharp-slit/low-fan theorem remains unproved; completing that theorem would
combine with this branch to settle the prism type. That implication is a
research roadmap, not a claim that the missing theorem already holds.
