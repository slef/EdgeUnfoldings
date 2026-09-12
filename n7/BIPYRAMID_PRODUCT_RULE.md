# One local test at every inward corner

**13 September 2026 · A stronger proved sufficient rule.** The rule works
for every convex bipyramid, with any number of ring vertices, provided
its local tests pass at one pole. It includes cases outside both supporting
half-spaces. Some exact examples fail the tests at both poles, so this is
not being presented as a complete solution.

The pentagonal bipyramid remains open; **7/15 whole patch classes** are
proved. This page gives a sharper description of the remaining geometry,
not another complete symbolic class.

[Overview](index.html#bipyramid) · [Supporting-plane theorem](BIPYRAMID_SOURCE_PLANE.html) ·
[Ordered-run theorem](BIPYRAMID_RUNS.html)

## The rule in geometric terms {#rule}

For each ring edge $u_i u_{i+1}$, flatten just its two incident triangles.
Let $D_i$ be the resulting distance between the two pole copies. This
length is independent of which pole is used as fan.

At an **inward ring corner** $a=u_i$, put

$$S_i=D_{i-1}D_i,\qquad H_i=|pu_i|^2-|qu_i|^2.$$

**Theorem Product Rule.** If

$$H_i\le S_i\quad\text{at every inward ring corner}, \qquad(1)$$

cut the star at source $q$, and slit the fan $p$ at a vertex maximizing
$|pu_i|+|qu_i|$. The entire edge unfolding is nonoverlapping.

To try the other source, change $H_i$ to $-H_i$. The $D_i$ do not change.
In the pentagonal case this means checking at most four scalar inequalities
at each pole. Weak inequalities and tied slit maxima are included in the
written theorem.

The test uses the actual edge lengths of the polyhedron. The two-face
developments compute five lengths; they are not a numerical experiment
standing in for the proof.

![The signed local ratios for an exact passing four-inward example and an exact three-inward conflict.](figures/bipyramid-product-test.svg)

*Each dot is the ratio $H_i/S_i$ at one inward corner. Positions are rounded illustrations of the exact bounds in the linked certificates.*

## Why a failed angular ordering violates the product bound {#proof}

Use $p$ as fan and $q$ as source. The
[supporting-plane proof](BIPYRAMID_SOURCE_PLANE.html#order) established the
following reduction. Any reversal in the angular order of neighboring
source copies, in one of the relevant forward or backward combinations,
puts a copy $M$ strictly in the preceding indentation

$$\operatorname{conv}\{a,p,P\},\qquad |aM|=|aP|=s.$$

After reflection if necessary, their angles from ray $pa$ are
$0<\beta<\alpha<\pi$, where $P$ has angle $\alpha$ and $M$ has
angle $\beta$. Write $D=|pP|$, $E=|pM|$, and $r=|pa|$.

First, $E<D$. To see this directly, normalize $a$ to the origin,
$P$ to polar angle zero, $p$ to angle $\delta\in(0,\pi)$, and $M$
to angle $\eta\in(0,\delta)$. Both copies lie on the radius-$s$ circle.
Then

$$E^2=r^2+s^2-2rs\cos(\delta-\eta)
<r^2+s^2-2rs\cos\delta=D^2.$$

The cosine rule in the two triangles with base $pa$ now gives

$$\cos\alpha-\cos\beta
=\frac{D-E}{2r}\left(1-\frac{r^2-s^2}{DE}\right).$$

The left side is negative, while $D-E>0$. Therefore

$$|pa|^2-|qa|^2>DE=D_{i-1}D_i.$$

This is exactly a violation of (1). Thus (1) excludes every source-ray
reversal. The
[complete pair separation argument](BIPYRAMID_SOURCE_PLANE.html#separation)
then proves the net safe: consecutive inward runs use outer-triangle
clipping, different runs have disjoint angular cones, and the maximal
slit prevents a crossing of the opened gap.

No pole-curvature hypothesis is needed.

## The simple plane test only needs the inward corners {#corners}

Let $L=|pq|$. Every opened two-face pole distance satisfies $D_i>L$,
so $S_i>L^2$. Consequently it already suffices that

$$|pu_i|^2-|qu_i|^2\le L^2$$

**at inward corners only**. Equivalently,

$$(u_i-q)\cdot(p-q)\ge0$$

at those vertices. The other ring vertices may project beyond $q$.
This strengthens the whole-ring condition in the earlier theorem.

The product test is stronger still: it can pass even when some inward
corners project beyond the source plane. An exact four-inward example
below passes at both poles although the inward-corner plane test fails
at both.

## A concrete remaining obstruction {#remaining}

The two pole choices both fail this sufficient rule precisely when there
are inward corners $u_a,u_b$ with

$$H_a>S_a,\qquad H_b<-S_b.$$

Since $S_i>L^2$, these corners project beyond opposite ends of the
pole-to-pole segment. This identifies an actual conflict between two
local conditions; it is much more specific than an unspecified possible
overlap between distant faces.

Such conflicts do occur. The [exact records](results/bipyramid-product-rule.json)
include a previously solved two-inward shape and still-open three-inward
patterns with strict failures at both poles. The two-inward example is
covered by the separate complete chain proof. These are failures of
**the sufficient test**, not counterexamples to edge unfoldability.

The eight open classes now separate into two precise next targets:

| Still-open classes | Structure and next question |
| --- | --- |
| BBBCC, BBFCC, BBBBC, BBBFC, BBFFC | All inward patches form one consecutive block. Conjecture: at least one source always passes the product test. This is **not proved**. |
| BBCBC, BBCFC, BCBFC | Two blocks of inward patches. Exact examples above show that both source tests can fail, so a repair or a different rule is necessary for this criterion to cover the whole class. |

A floating search of 1,327,019 numerically accepted samples found strict conflicts
in the latter three classes and none in the former five. The three
conflicts were converted to exact certificates. The absence of a sampled
conflict in the five single-block classes is only a reason to investigate
the conjecture; it is not a coverage claim or part of a proof.

A useful next step is to repair the two conflicting corners with the
pocket-and-disk lemmas already used for two inward patches, while checking
whether the additional third or fourth patch can reach that repair.

## Exact checks {#checks}

The [replay checker](bipyramid_product_rule.py) verifies strict convexity,
the interval bounds for all developed diagonals, and the product tests.
For successful applications it independently checks all 45 face pairs.
For a claimed two-pole test failure it verifies a strictly negative
margin at each pole; it does not infer overlap from that sign.

All the universal claims above are geometric arguments. The exact examples
illustrate their scope and limitations; neither successful samples nor a
search without failures replaces any part of the proof.
