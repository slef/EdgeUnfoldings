# The paired-pole rule: an octahedron and minus-edge proof without switching

12 September 2026, final review pass. This is a newly shortened written
research proof, pending independent mathematical review. All preceding
proofs, the cap criterion and the earlier unproved shortcut are preserved.
Exact coefficient checks verify the identity below; numerical searches
are not premises of the theorem.

## The rule

On an octahedron, fix **any opposite pair**. Call its sharper endpoint v
and its other endpoint w. Among their four equator vertices, choose a
sharpest c. Cut the four edges at v and the edge wc. This whole net has
disjoint face interiors. All ties may be resolved either way.

Thus the source need only be at least as sharp as its opposite, rather
than sharpest among all six vertices. There is no comparison between the
curvature differences of different pairs and no trial unfolding.

An equivalent useful option is to choose a globally sharpest c first,
set aside its opposite, and use either remaining opposite pair, oriented
from sharper source to less sharp fan. For that option the projection
argument E1 is unnecessary, as explained below.

## The identity that removes the last angle condition

Use the three-patch Case A setup in [TIDY_CORE.md](TIDY_CORE.md). The middle
petal has apex angle nu and base vertices u,u' with total curvature
K=kappa_u+kappa_(u'). The two outer petals have apex angles lambda,rho.
Put theta=pi-nu+K, so Case A is 0<theta<pi.

There is exactly one other petal. Write eta for its apex angle, a,b for
its base vertices, and xi,zeta for its angles at a,b. Define the two
strict link slacks

    s_a=(2*pi-kappa_a)-2*xi > 0,
    s_b=(2*pi-kappa_b)-2*zeta > 0,
    S=s_a+s_b.

Their positivity is the closed spherical-link lemma. The original face
and vertex angle sums give

    eta+lambda+nu+rho=2*pi-kappa_v,
    xi+zeta=pi-eta,
    kappa_v+kappa_w+K+kappa_a+kappa_b=4*pi.

Eliminating eta and the two complementary curvatures gives

    2*pi+K-2*lambda-nu = (kappa_v-kappa_w)+S+nu+2*rho,
    2*pi+K-2*rho-nu    = (kappa_v-kappa_w)+S+nu+2*lambda.

When kappa_v>=kappa_w, both right sides are strictly positive. Therefore

    lambda < (pi+theta)/2,   rho < (pi+theta)/2.

These are exactly the two sufficient bounds in the wider Case A lemma.
Its angle-sum premise holds because lambda+rho+nu<2*pi-kappa_v<2*pi+K.
The strict distance-sum inequality supplies a short copied edge, and that
lemma separates the whole two petals. **Every opposite-petal Case A is
safe whenever the source is at least as sharp as its opposite.**

No cap upper bound, obtuse/nonobtuse split, maximum-curvature hypothesis,
or numerical feasibility claim is used in this identity. The fourth
petal is essential: its two base-angle link slacks provide the remainder.
Flat auxiliary hinges are allowed, since all vertices are genuine and
the spherical-link inequalities remain strict.

## Completing the same whole net

For clarity, the following slightly broader criterion suffices:

    kappa_v>=kappa_w,
    2*kappa_c+kappa_w>=pi,
    either kappa_v>=pi or both slit-adjacent blue-face
        curvature sums are at least pi.                 (P)

The geometric steps are written out in [the shared core](TIDY_CORE.md):

1. The source order implies its half-fan alternative: either the fan is
   at most pi, or the source is above pi too. The weighted slit threshold
   then settles the three local pairs and strictly separates each local
   petal from the opposite closed slit segment.
2. A remote petal touching a finite slit would force both E1, kappa_v<pi,
   and E2, kappa_a+kappa_c+2*kappa_w+2*mu<pi. The last premise of (P)
   therefore supplies the blue-face lower bound, contradicting E2.
3. Case A is settled by the new identity. The large-fan Case B is already
   separated by the base cones. A small-fan overlap would force
   nu_0>kappa_a+kappa_c+kappa_w. If kappa_v>=pi, the link bound gives
   nu_0<pi/2, whereas the slit threshold gives kappa_c+kappa_w>pi/2.
   Otherwise the blue-face lower bound forces nu_0>pi, also impossible.
4. The four target-boundary checks finish the remaining petal/fan pairs.
   With the 19 shared-vertex pairs, this accounts for all 28 pairs in this
   one net. It does not invoke the refuted unrestricted hinge reduction.

To apply (P) to the fixed-pair rule, choose an equator maximum c. Then

    2*kappa_c+kappa_w >= 2*pi-kappa_v/2+kappa_w/2 > pi.

If kappa_v>=pi, the last premise of (P) holds directly. Otherwise w is
also below pi. If c>=pi, both blue-face sums exceed pi. If c<pi, all six
curvatures are below pi, so the three complementary curvatures sum below
3*pi and each blue face has curvature sum above pi. These alternatives
include every equality and prove the rule.

If c was chosen globally sharpest instead, each triple containing c has
curvature sum above pi: if one summed to at most pi, then c and the three
complementary vertices would all be below pi, contradicting total 4*pi.
Also kappa_c>=2*pi/3 makes the slit threshold automatic. Thus (P) applies
for either remaining oriented pair. In this version the lower blue-face
bounds contradict E2 directly, so E1 can be omitted entirely.

## The minus-edge graph now needs no source switch

Label the original facets as before: ACBD, ACP, APQ, ADQ, BDQ, BPQ, BCP.
The two nonadjacent quadrilateral corners A,B each have degree four and
are joined to every other vertex. Add CD as an uncut flat hinge.

Fix opposite pair A,B. Take its sharper endpoint as v, the other as w,
and choose c with largest curvature among C,D,P,Q. Every edge in star(v)
and every possible wc is original. The paired-pole rule therefore gives
a nonoverlapping net, and the uncut CD rejoins the original quadrilateral.

This replaces the complete source-switch exhaustion for this type by one
rule. The earlier complementary-source identity, switching proof, examples
and counterexamples remain available for future work. It does not settle
the separate conjecture about two particular fixed trees.

## What the exact checks establish

The [saved exact report](results/paired-poles.verification.json) records 38
independent selected-net replays. The [checker](paired_poles.py) expands all 16 reflected and cyclic versions of the two
identities as exact rational polynomials in 16 independent face-angle
variables. Each residual is identically zero. Its selector checks actual
uniform curvature orders and independently verifies the entire chosen net
on an explicit point or parameter domain. It may reject a box on which
one uniform order cannot be established; that is not a failure of the
pointwise mathematical rule.

The earlier integer example where the unranked choice failed an upper cap
bound is now covered by this proof: its wider angle bounds suffice instead.
The [previous investigation](OCTA_UNRANKED_BEFORE_IDENTITY.html)
and its exact example are preserved. The wider-angle identities were
suggested by a numerical linear optimization, but their displayed exact
expansion and strictly positive remainder are the proof of the inequalities.
The universal geometric argument still requires independent review.
