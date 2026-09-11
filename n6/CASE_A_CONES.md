# Case A: the complete planar apex-cone argument

11 September 2026. This restates the existing Case A proof from the
repository's `durer_small_n/notes/lemmaF.tex` and makes the strict
distance-sum step explicit. It is a dependency exposition, not a newly
discovered family or a change to the progress count.

## Setup and required inequalities

Take three consecutive fan triangles and their orange petals. The middle
petal has base u=(0,0), u'=(ell,0), apex M above the base, base angles
phi,psi, and apex angle nu. Let P and Q be the developed apices of the
left and right petals; their apex angles are nu_left and nu_right.
Put

    kappa = kappa_u+kappa_u',
    alpha = phi+kappa_u,
    beta  = psi+kappa_u'.

Case A means kappa<nu. Consequently alpha,beta>0 and

    alpha+beta = pi-nu+kappa < pi.

The only additional hypotheses for the planar argument are

    nu_left <= alpha+beta,
    nu_right <= alpha+beta.                         (N)

The ray uP has direction alpha, and the ray u'Q direction pi-beta.
The two copies of each original cut edge have equal lengths:

    |uP|=|uM|=:s,    |u'Q|=|u'M|=:s'.

All the triangles are nondegenerate. These facts remain true when an
auxiliary hinge elsewhere on the original surface is flat.

## 1. Both cut segments cannot reach their line intersection

The two rays meet above the base at p*. Since alpha>phi and beta>psi,
the middle apex M is strictly inside triangle uu'p*. This follows from
its two strict base-angle comparisons: it lies above the base and on
the interior side of both other sides.

Define the convex function f(x)=|ux|+|u'x|. At either base endpoint it
equals ell, whereas f(p*)>ell by strict triangle inequality. Write M as
a convex combination of the three vertices, with its p* coefficient
t strictly between 0 and 1. Convexity gives

    f(M) <= (1-t)*ell+t*f(p*) < f(p*).

If both cut segments reached p*, we would have |up*|<=s and |u'p*|<=s',
giving f(p*)<=s+s'=f(M), a contradiction. This includes a proposed
intersection at an endpoint of either cut segment.

## 2. The apex cones can meet only if both cut segments reach p*

The left petal lies in its apex cone at P, with direction interval

    I = [pi+alpha-nu_left, pi+alpha].

The right petal lies in its apex cone at Q, with direction interval

    J = [-beta, -beta+nu_right].

These intervals use the actual orientations of the two petals: the left
one is on the left of uP, and the right one on the right of u'Q. Each
cone has width below pi because it is a triangle's apex angle.

The reversed right cone has interval -J=[pi-beta,pi-beta+nu_right].
By (N), both I and -J lie in the convex sector

    S=[pi-beta,pi+alpha],

whose width is alpha+beta<pi. Their extreme boundary rays include both
extremes of S, so their vector sum is exactly S. The translated apex
cones meet only if Q-P belongs to S.

Let e1 be the unit vector of direction pi+alpha and f2 the unit vector
of direction pi-beta. They are linearly independent. With e0=(1,0),

    Q-P = s*e1+ell*e0+s'*f2,
    e0 = -sin(beta)/sin(alpha+beta)*e1
         -sin(alpha)/sin(alpha+beta)*f2.

The sine rule in triangle uu'p* therefore gives

    Q-P = (s-|up*|)*e1+(s'-|u'p*|)*f2.

Membership in S requires both coefficients nonnegative, which says
precisely that both cut segments reach p*. Section 1 excludes this.
Thus the two apex cones, and hence the petals, have disjoint interiors.

## 3. Where the no-wrap hypotheses come from

Put G=2*pi-kappa_v, the sum of the four orange apex angles.
Condition (N) is equivalent to

    nu_left+nu <= pi+kappa,
    nu_right+nu <= pi+kappa.

Each left side is at most G. The following sufficient cases are used
in the current octahedron proofs:

* Under H, the other four vertices each have curvature<=kappa_v, so
  kappa>=4*pi-4*kappa_v=4*G-4*pi. If G>=pi, then
  pi+kappa>=4*G-3*pi>=G. If G<pi, the bound is immediate.
* If kappa_v>=pi, then G<=pi, so both inequalities are immediate
  without a global maximum hypothesis.
* If every curvature<=pi, the three vertices other than v,u,u' have
  total curvature<=3*pi. Thus kappa>=pi-kappa_v and
  pi+kappa>=2*pi-kappa_v=G, again without a ranking hypothesis.

This proves Case A under every source condition used by the selected,
source-choice, weighted-slit, and flat-hinge theorems. It uses no local
Lemma L premise, no slit ranking, and no strict dihedral-angle condition.
The separate base-cone and small-fan branches complete the exhaustive
partition recorded in [CASE_PARTITION.md](CASE_PARTITION.md).
