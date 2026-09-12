# A whole run of inward patches: one ordering test

**13 September 2026 · A proved family inside the remaining three- and
four-inward cases.** The following theorem allows any number of consecutive
inward patches in a convex bipyramid. It gives an explicit sufficient
rule, not a claim that some pole always passes that rule.

The whole pentagonal bipyramid remains open. The complete class count
stays **7/15**. This theorem supplies additional proved parts of the
consecutive three-inward class BBBCC and four-inward class BBBBC.

[Overview](index.html#bipyramid) · [Final two-inward proof](BIPYRAMID_ADJACENT.html) ·
[Radial lemmas](BIPYRAMID_RADIAL.html)

## 1. A rule that scales with the length of the run {#rule}

Suppose $Q_0,\ldots,Q_{k-1}$ are inward and all point forward. Every
remaining patch is convex. Let the ring have $m\ge k+1$ vertices.
Choose a fan pole $p$, and let

$$\theta_i=\sum_{j<i}\omega_j^p,
\qquad E_i=\theta_{i+1}+\ell_i^p\quad(0\le i<k).$$

The angle $E_i$ is where inward patch $i$ ends around that pole. Its
whole angular cone is $[\theta_i,E_i]$.

**Theorem Ordered Run.** If

$$E_0\le E_1\le\cdots\le E_{k-1}\le\theta_{k+1},$$

then cutting the other pole's edge star and the edge $pu_0$ gives a
nonoverlapping original-edge unfolding.

In ordinary language: the bad patches end in the same order in which
they begin, and the last one does not pass its first convex neighbor.
The test is just

$$\ell_i^p\le\omega_{i+1}^p+\ell_{i+1}^p\quad(0\le i<k-1),
\qquad \ell_{k-1}^p\le\omega_k^p.$$

There is no pole-curvature ranking, curvature threshold, or planar-equator
assumption. All the weak inequalities, including equality, are allowed.
Reflection gives the corresponding backward-run theorem.

## 2. Filling an inward patch without harming its predecessor {#hulls}

Let $P_i$ be the source copy in patch $Q_i$, and write

$$H_i=\operatorname{conv}\{p,u_i,P_i\}.$$

This is the outer triangle containing the bad patch; its inward vertex
$u_{i+1}$ is strictly inside $H_i$.

The preceding patch $Q_{i-1}$ is safe against the **entire** triangle
$H_i$. At their shared, uncut vertex $u_i$, the angular corner of $H_i$
is exactly the corner occupied by the two faces of $Q_i$. Those sectors
and the preceding patch's sectors have total angle below $2\pi$.
Filling the missing triangle at the far endpoint adds no angular sector
at the shared endpoint.

There is also a clipping observation. The convex triangle $H_{i+1}$
contains $p$ and is safe against $Q_i$. Where an interior point of
$H_{i+1}$ lies inside $Q_i$'s angular cone, the radial segment from $p$
to it cannot cross the cut side $u_{i+1}P_i$ into the bad petal.
Consequently that portion of $H_{i+1}$ lies inside $H_i$.
This is the same [clipped-receiver argument](BIPYRAMID_ADJACENT.html#containments),
with an outer triangle in place of the final convex patch.

Only interior overlap is being tested. A boundary ray touching a cone
does not need a separate strict containment assertion.

## 3. Propagate the separation along the run {#proof}

Fix $i$. The adjacent-vertex argument gives that $Q_i$ is safe against
$H_{i+1}$. Suppose it has already been shown safe against $H_j$.
Any possible interior overlap with $H_{j+1}$ has angle below $E_i\le E_j$
and above $\theta_{j+1}>\theta_j$. It therefore lies inside the angular
cone of $Q_j$. The clipping observation puts that overlap inside $H_j$,
a contradiction.

By induction, $Q_i$ is safe against every later outer triangle $H_j$.
Since $Q_j\subset H_j$, all pairs of inward patches are safe.

The first convex patch $Q_k$ is safe against its adjacent predecessor
$Q_{k-1}$. For an earlier $Q_i$, any possible overlap with $Q_k$ lies
in the cone of $Q_{k-1}$ because $E_i\le E_{k-1}$. The same clipping
argument places it inside $H_{k-1}$, already safe against $Q_i$.
Thus every bad patch is safe against $Q_k$ as well.

Finally, $E_i\le E_{k-1}\le\theta_{k+1}$ prevents every bad patch
from reaching any later convex patch. Those convex patches have disjoint
fan wedges. There is no extension across the slit before $Q_0$.
This checks every face pair and proves the theorem for any run length.

## 4. Precisely what is missing for a whole three-inward class {#remaining}

For a three-patch forward run, define the three margins

$$G_0^p=\omega_1^p+\ell_1^p-\ell_0^p,
\quad G_1^p=\omega_2^p+\ell_2^p-\ell_1^p,
\quad G_2^p=\omega_3^p-\ell_2^p.$$

The theorem applies if either pole makes all three margins nonnegative.
The adjacent corner identities give

$$G_0^p+G_0^q=\kappa_{u_1}>0,\qquad
G_1^p+G_1^q=\kappa_{u_2}>0,\qquad
G_2^p+G_2^q>0.$$

Thus no individual comparison can fail at both poles. What is still
missing is a proof that a **single** pole can be used, or a repair when
different comparisons prefer opposite poles.

A failure of the two-pole ordering test must contain opposite preferences
in at least one of these three pairs of tests:

| Pair of comparisons | Geometric issue |
| --- | --- |
| $G_0,G_1$ | The two internal endpoint orderings prefer opposite poles |
| $G_0,G_2$ | The first ordering conflicts with keeping the last receiver short |
| $G_1,G_2$ | The second ordering conflicts with keeping the last receiver short |

These are three possible **obstruction types**, not three proved-realizable
metric families or percentages of proof completion. They may overlap.
For four inward patches the same theorem uses four comparisons, leaving
six possible pairs of opposing preferences.

The [adjacent-two-patch proof](BIPYRAMID_ADJACENT.html) already resolves
the corresponding two-test conflict for a run of length two. Extending
that pocket-and-disk repair through one more patch is a concrete next target.

## 5. Exact examples and limits {#checks}

[Exact applications](results/bipyramid-runs.json) cover one three-inward and two four-inward shapes, all with both pole
curvatures below $\pi$. The poles are displaced from a common perpendicular
line, so these examples also go beyond the aligned-pole family. They verify the ordering
inequalities and independently check all 45 face pairs for three- and
four-inward examples. The [replay checker](bipyramid_runs.py) uses rational
angle bounds. The proof covers every realization satisfying the displayed
inequalities; it does not infer a universal pole-choice theorem from
successful examples or from searches that found no failure.
