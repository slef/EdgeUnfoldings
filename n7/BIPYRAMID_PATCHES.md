# Five patches: what transfers from the octahedron

12 September 2026. Separate seven-vertex research. **The pentagonal bipyramid
is still open in general.** The conditional theorems below are geometric
arguments; the accompanying finite counts and examples have different scopes.

**New route, 13 September:** [grow the solid from six vertices](BIPYRAMID_MORPH.html).
Convexity and monotone curvature are proved; carrying a safe net throughout
remains open in general. The aligned-pole insertion is now proved, and the
complete chain rule raises the count below to four.

**Overnight extension:** [the length-sum slit theorem](BIPYRAMID_OVERNIGHT.html#length-slit)
settles the local pairs for every convex bipyramid. The [two-patch rules](BIPYRAMID_OVERNIGHT.html#two-gap)
prove larger curvature branches. The subsequent chain theorem raises the
whole-class count to **4/15**.

**Further family theorem:** [aligned poles](BIPYRAMID_ALIGNED.html) are now
covered at every height, including four inward patches with low pole
curvatures. The [shortest-patch theorem](BIPYRAMID_STAR_PATCH.html) covers
all large-pole cases without alignment. Whole-class counts are unchanged.

## Setup: ten triangles, five simple candidate cuts

Let $v,w$ be the two nonadjacent degree-five poles. Write the equator in
cyclic order as $u_0,\ldots,u_4$, and put

$$W_i=w u_i u_{i+1},\qquad V_i=v u_i u_{i+1},\qquad Q_i=W_i\cup V_i.$$

Indices are taken modulo five. Flatten each two-face patch along its equator
edge; this is a separate local operation, not an assertion that the five
copies of $v$ coincide. Write $\omega_i$ and $\nu_i$ for the angles at $w$
and $v$, and $e_i,f_i$ for the flattened patch's angles at $u_i,u_{i+1}$.
Then

$$\omega_i+\nu_i+e_i+f_i=2\pi,\qquad
 f_{i-1}+e_i=2\pi-\kappa_{u_i}.$$

Cut the five edges at one pole, plus one edge from the other pole to the
equator. This is an original-edge spanning tree. The uncut faces form a
fan at the second pole with one petal attached to each fan triangle.
There are five possible slits at each of the two poles: ten candidates.

A patch is **C** if $e_i,f_i\le\pi$, **B** if $e_i>\pi$, and **F** if
$f_i>\pi$. Thus B and F indicate which equator corner is inward. A patch
cannot have both corners inward. A straight corner is included in C.
These are geometric conditions, not properties determined by the graph.

## 1. At least one patch is strictly convex — for any ring size

This old four-patch fact has no four-patch restriction. Put
$d_i=|vu_i|+|wu_i|$. If the patch has a corner at least $\pi$ at $u_i$,
then $d_i<d_{i+1}$; the reflected statement also holds.

For a reflex corner, $u_i$ lies inside the triangle formed by the other
three flattened vertices. The convex function $x\mapsto |x-v_i|+|x-w|$
takes the common value $|v_iw|$ at the poles and the strictly larger value
$d_{i+1}$ at the other equator vertex. A convex combination gives the strict
inequality. For a straight corner, $u_i$ lies on the segment $wv_i$, so
$d_i=|wv_i|<d_{i+1}$ directly.

Two patches cannot have corners at least $\pi$ at the same equator vertex:
their corner sum is $2\pi-\kappa_{u_i}<2\pi$. If all five patches failed
to be strictly convex, their large corners would therefore occupy distinct
vertices. But a vertex maximizing $d_i$ cannot be any such corner. This is
a contradiction. The proof is unchanged for any suspension with $m\ge3$
equator vertices.

This excludes the putative family with five inward patches. It does not
exclude four inward patches or prove the whole net safe.

## 2. All convex patches give an entire net {#theorem-c}

**Theorem C.** If every patch is C, all five slits work at either pole.

A convex patch lies in the angular wedge of its fan triangle at the fan
pole. The fan wedges have disjoint interiors and total angle strictly
below $2\pi$. Within a patch its two triangles are on opposite sides of
the equator edge. All ten faces are therefore interior-disjoint.

In particular this holds if every original triangular face is nonobtuse:
each equator patch angle is the sum of two angles at most $\pi/2$.
This recognizable geometric family includes an explicit open neighborhood
of the rational-coordinate example in the accompanying exact report.
The same theorem holds for any ring size.

## 3. Exactly one inward patch is also completely covered {#theorem-one}

**Theorem One.** A convex suspension with exactly one inward patch has a
nonoverlapping original-edge net among its two-pole star-plus-slit candidates.
There is no sharpest-vertex or curvature-ranking hypothesis.

Reflect and rotate so that the bad patch is $Q_0$ and is F. Let $\ell_0^w$
and $\ell_0^v$ be its positive angular extensions beyond its own fan wedge
when viewed from the two poles. Comparing the outer triangle of the concave
quadrilateral with the quadrilateral itself gives

$$\ell_0^w+\ell_0^v=f_0-\pi=:\rho_0.$$

The shared corner at $u_1$ and the angle sum of the following, convex patch
$Q_1$ give an exact identity:

$$\rho_0-(\omega_1+\nu_1)=f_1-\pi-\kappa_{u_1}<0.$$

Consequently one pole $p$ has $\ell_0^p<\angle_p(Q_1)$. Choose it as the
fan pole, cut the other pole's star, and put the slit at $p u_0$.
The first patch extends only forward. Its cone ends before the end of the
second fan wedge, so it cannot reach any patch $Q_2,Q_3,Q_4$. All those
patches are convex. $Q_0$ and $Q_1$ are safe by their common uncut equator
vertex, where the four triangles form consecutive wedges of total angle
less than $2\pi$. There is no backward extension across the slit.
This checks every pair.

The argument also specifies a rule: compare the bad patch's extension at
one pole with that pole's angle on the next patch. If the strict inequality
fails, the other pole satisfies it. Equality at the first pole causes no
problem. The proof only uses that the next patch is convex and all other
patches are convex, so it works for any ring size.

## 4. Two inward patches pointing into the same convex patch {#theorem-toward}

**Theorem Toward.** Suppose only $Q_0,Q_2$ are inward, $Q_0$ is F and
$Q_2$ is B. Thus they both point toward the intervening convex patch $Q_1$.
One of the two pole choices with slit at $u_0$ gives an entire safe net.

Set $\rho_0=f_0-\pi$ and $\rho_2=e_2-\pi$. Add the full angle identities
at $u_1,u_2$ and subtract the angle sum of $Q_1$:

$$\rho_0+\rho_2=
\omega_1+\nu_1-\kappa_{u_1}-\kappa_{u_2}<\omega_1+\nu_1.$$

Since each $\rho_i=\ell_i^w+\ell_i^v$, at least one pole satisfies
$\ell_0^p+\ell_2^p<\angle_p(Q_1)$. Choose that pole as the fan center.
With slit $p u_0$, the cones of $Q_0,Q_2$ are separated across $Q_1$.
Neither reaches any more distant patch. Each is safe against $Q_1$ by the
common-vertex fan argument, and all other patches are convex. There is no
extension across the slit. All pairs are safe. Again no curvature order
is required, and the same proof works for any ring size at least four.

This theorem concerns a **single** intervening convex patch. At five
vertices on the ring there is also an opposing-direction pattern whose
inward corners point toward a chain of two convex patches. The displayed
identity does not by itself settle that different case; the following theorem does.

## Two convex receivers: the complete opposing-chain rule {#theorem-chain}

**Theorem Chain.** Pattern FCCBC (canonical BCFCC) has a safe star-plus-slit
net for every convex realization, without a pole-curvature condition.
Choose a pole whose two bad extensions sum to less than the two receiver
angles. If the other pole has both extensions short, it may be used instead.
Otherwise the first pole works: the long extensions force the exact apex
bounds needed to separate the last petal pair.

The [complete proof and finite rule](BIPYRAMID_CHAIN_RULE.html) explain
why a long extension into a convex receiver forces an acute fan angle.
This closes one further entire symbolic class, rather than just examples.

## 5. A further family when one pole has curvature at least pi {#theorem-gap}

**Theorem Gap.** Suppose precisely two adjacent patches are inward and
lean in the same cyclic direction. If one pole has curvature at least
$\pi$, use that pole as fan center. A slit immediately after the two
forward patches, or before the two backward patches, gives a safe net.

Each inward patch's full angular cone at the fan pole has width below
$\pi$, hence its extension is below $\pi$. The fan gap has size at least
$\pi$. In the forward case put the two bad patches last in the fan.
Their cones can meet each other, but these are adjacent patches and are
safe by the common-vertex fan. Their forward extensions do not wrap across
the gap to any earlier convex patch. Neither has a backward extension.
All other pairs lie in convex wedges. Reflection proves the backward case.
The equality $\kappa_p=\pi$ is included. This is a conditional part of one
additional pattern, not a proof of that pattern for all curvatures.

## 6. Lemma L extends locally, with an explicit threshold {#lemma-l7}

**Theorem L7.** In a convex suspension with any ring size, choose source
$v$, fan pole $w$, and slit $wu$. If

$$\kappa_v\ge\kappa_w,\qquad 2\kappa_u+\kappa_w\ge\pi,$$

then the three local face pairs beside the slit are safe: the two flank
petals against one another and each against the opposite flank fan triangle.
This makes no assertion about other face pairs.

Here is the proof with the ring-size dependence exposed. Let
$\Gamma_p=2\pi-\kappa_p$. For an edge direction $pu$ and the interior
pole direction $pq$, the convex spherical link gives
$2\angle(upq)<\Gamma_p$. Omitting one link side of length $\omega$ incident
to $pu$ also gives $\angle(upq)<\Gamma_p-\omega$: the great-circle ray
through the interior direction exits the remainder of the link. These
statements do not depend on its number of sides.

Consider the original pole triangle $wuv$, with angles $\alpha$ at $w$
and $\beta$ at $v$, and side lengths $r=|wu|,s=|vu|,D=|wv|$.
A flank patch extending toward the fan interior has its other corner
inward. Its outer triangle has side $t=|wP|\ge D$, by the spherical angle
triangle inequality at $u$ and the cosine law. If $\beta\le\pi/2$, then

$$\cos\gamma(t)-\cos\gamma(D)
=\frac{(t-D)(tD-r^2+s^2)}{2rtD}\ge0,$$

so its full angle $\gamma$ at $w$ is at most $\alpha$. Two extending
flanks therefore sum to less than $\Gamma_w$; for just one, the omitted-side
link bound leaves the opposite flank's fan angle free. If $\beta>\pi/2$,
then $r^2>D^2+s^2$, so each such $\gamma<\pi/2$. The link at $v$ implies
$\kappa_v<\pi$, and the pole comparison implies $\Gamma_w>\pi$.
For one extending flank use the other face angle at most $\Gamma_w/2$;
for two use their sum below $\pi$. Thus the cones cannot meet through
the intervening fan in either case, however many middle faces it contains.

Across the slit, at most one flank is inward at $u$. If there is one,
let its excess corner angle be $\rho>0$ and its across-slit extension $B$.
The two flank corner sums give

$$0<B<\rho<\pi-\kappa_u.$$

If $B\le\kappa_w$ the gap separates the cones. Otherwise write the two
copies of $u$ as $A=(r,0)$ and
$A'=r(\cos\kappa_w,-\sin\kappa_w)$. The offending petal lies left of
its own cut edge in direction $d=(\cos\rho,-\sin\rho)$, whereas

$$\det(d,A'-A)=-2r\sin(\kappa_w/2)\cos(\rho-\kappa_w/2)<0.$$

Indeed $0<\rho-\kappa_w/2<\pi-\kappa_u-\kappa_w/2\le\pi/2$.
All directions into the opposite patch, measured relative to $d$, lie in
$[\rho-\pi-\kappa_w,-\kappa_u-\kappa_w]\subset(-\pi,0)$.
That whole patch is therefore strictly right of the cut line. The remaining
local pair has neither an across-slit extension nor a through-fan route.
Reflection handles the other inward flank. This proves all three pairs,
including equality in the stated threshold.

### What the maximum-curvature slit guarantees at seven vertices

For the sharper pole as source, and an equator maximum $c$,

$$2\kappa_c+\kappa_w\ge
\frac{8\pi-2\kappa_v+3\kappa_w}{5}.$$

Thus L7 is automatic whenever $2\kappa_v-3\kappa_w\le3\pi$; in particular
whenever the sharper pole's curvature is at most $3\pi/2$.
This covers a substantial explicitly described local branch, not the whole net.

The six-vertex automatic deduction cannot be copied without this condition.
For example the relaxed assignment, in units of $\pi$,

$$\kappa_v=1.8,\quad\kappa_w=0.1,\quad
\kappa_{u_0}=\cdots=\kappa_{u_4}=0.42$$

sums to 4 and satisfies the pole comparison and equator-maximum rule, but
$2\kappa_c+\kappa_w=0.94<1$. This is only a counterexample to a deduction
from those curvature constraints. We have not proved that assignment is
realizable by this graph; it is not a polyhedral counterexample to the rule.

## 7. A finite pattern map, with honest denominators

Consecutive symbols F,B are impossible because both inward corners would
be the same equator vertex. All-F and all-B cycles are impossible by the
strict $d_i$ inequalities. These exclusions leave **121 labelled symbolic
patterns**, or **15 classes** after rotations and reflection (reflection
also swaps B and F). We do not claim that every admitted symbolic pattern
has a convex realization. This is an exhaustive necessary partition.

| Inward patches | Labelled patterns | Symmetry classes | Entire classes covered here |
| --- | ---: | ---: | ---: |
| 0 | 1 | 1 | 1, Theorem C |
| 1 | 10 | 1 | 1, Theorem One |
| 2 | 35 | 5 | 2, Theorems Toward and Chain; the other three have proved curvature branches |
| 3 | 50 | 5 | 0 |
| 4 | 25 | 3 | 0 |
| 5 | 0 | 0 | impossible |

The four fully covered representatives are CCCCC, BCCCC, BCCFC, BCFCC in the
catalogue's canonical convention. Thus **4/15 symbolic classes have whole
conditional existence proofs**; 11 retain open parts. Theorem L7 settles
three local pairs under its additional inequalities across many of them.
The [new local selection theorem](BIPYRAMID_OVERNIGHT.html#length-slit)
removes the threshold when the slit may be chosen by the distance-sum rule.
Neither count changes the bipyramid graph's overall open status.

## Exact example and boundary of the certificate

The rational example has poles $(0,0,1),(0,0,-1)$ and ring

$$(1,0,0),\ (3/5,4/5,0),\ (-3/5,4/5,0),\ (-1,0,0),\ (0,-1,0).$$

For the independent coordinate interval of half-width $1/1000$ at each
of its 21 coordinates, rational interval arithmetic checks strict support
of all ten facets and positivity of all thirty corner dot products.
Every polytope in that box therefore has this graph and acute triangular
faces. Theorem C supplies all ten candidate nets throughout the box.
The equator need not remain coplanar under these perturbations.

This certificate checks a **specific open coordinate neighborhood**, and
invokes the written geometric theorem. It does not computationally certify
all realizations, and it is not a Lean proof. The general theorems above
do not use the example as a premise.
