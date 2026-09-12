# The remaining receiver pair: two branches settle, one angle test remains

**Later update, 13 September:** the [complete opposing-chain rule](BIPYRAMID_CHAIN_RULE.html) now closes the entire FCCBC / BCFCC class. The [radial extension](BIPYRAMID_RADIAL.html) brings the current count to **6/15**; the earlier reductions and open questions below are preserved as the record of how that result was reached.
The separator lemmas on this page remain part of the completed proof; its final unresolved row has been discharged by the new long-receiver lemma and pole-selection rule.

**13 September 2026 · A further written reduction.** In the opposing-chain
pattern, a long extension rules out the small-fan pocket altogether.
The large-angle branch is therefore solved by a direct cone separator.
The remaining small-angle branch has an explicit sufficient angle test,
and a new identity describes how the seventh vertex changes the n6 proof.
The whole pattern is not yet claimed solved.

[Receiver-chain reduction](BIPYRAMID_RECEIVERS.html#chain) ·
[Overnight results](BIPYRAMID_OVERNIGHT.html) ·
[Seven-vertex overview](index.html#bipyramid)

## 1. The one independent pair and its notation {#setup}

Take pattern FCCBC and choose the fan pole $p$ by the combined-extension
rule. Let $q$ be the other pole. Suppose $Q_0$ is the long patch:

$$\ell_0^p>\omega_1,\qquad
\ell_0^p+\ell_3^p<\omega_1+\omega_2.$$

Here $\omega_i$ are the face angles at the chosen fan pole. Slit at
$p u_0$. The only independent question is whether petals $V_0,V_2$
overlap; its solution also separates $V_0/W_2$ by the boundary argument.
Reflection handles a long $Q_3$ with middle patch $Q_2$ instead.

Develop the middle petal $V_1$ with base $a=u_1=(0,0)$,
$b=u_2=(d,0)$, and apex $M$ above the base. Its angles are
$\phi$ at $a$, $\psi$ at $b$, and $\nu$ at $M$. Let $P,R$ be the
apex copies in $V_0,V_2$, with apex angles $\lambda,\rho$ respectively.
Set

$$K=\kappa_a+\kappa_b,\qquad
\alpha=\phi+\kappa_a,\quad\beta=\psi+\kappa_b,\quad
\theta=\alpha+\beta=\pi-\nu+K.$$

Let $\sigma$ be the sum of the fan-face angles at $a$ in $W_0,W_1$,
and $\tau$ the corresponding sum at $b$ in $W_1,W_2$. If $a_0,b_0$
are the outer petals' base angles at $a,b$, the vertex sums give

$$\alpha+\sigma+a_0=2\pi,\qquad
\beta+\tau+b_0=2\pi.$$

All individual triangular face angles lie in $(0,\pi)$.
These local definitions do not use a ranking of the two poles.

## 2. A long receiver extension excludes the small-fan pocket {#no-pocket}

Write the inward corner of $Q_0$ at $a$ as $\pi+\eta$.
Let $h$ be $W_0$'s angle at $a$. Since the other part of that corner is
the triangular angle $a_0<\pi$,

$$h+a_0=\pi+\eta\quad\Longrightarrow\quad h>\eta.$$

The two-pole extension identity gives $0<\ell_0^p<\eta$.
The long-extension hypothesis therefore implies

$$h>\eta>\ell_0^p>\omega_1.$$

Write $x,y$ for the angles at $a,b$ in $W_1$, and $z>0$ for
$W_2$'s angle at $b$. As $x+y=\pi-\omega_1$,

$$\sigma+\tau=h+x+y+z
=\pi+(h-\omega_1)+z>\pi.$$

**Consequently the small-fan branch $\sigma+\tau<\pi$ is impossible.**
There is no need to extend the n6 pocket-containment argument in this
receiver problem. This is a universal angle deduction, not a search result.

### The receiver's source angle must be obtuse

There is also a useful geometric obstruction to a long extension. Put
$T=\operatorname{conv}\{a,p,P\}$, where $P$ is the bad patch's source
copy. Its side $aP$ is an actual boundary edge of the bad petal. The
receiver fan triangle $W_1$ starts inside $T$ near $p$. Its angular wedge
has width $\omega_1<\ell_0^p$, so it cannot leave through side $pP$;
side $pa$ is its own boundary. It cannot cross the open side $aP$,
because $W_1$ and the bad petal belong to the same uncut vertex fan at
$a$. Consequently $W_1\subset T$, with its open base $ab$ inside $T$.

The attached receiver petal $V_1$ starts inside $T$ along $ab$. Convexity
of $Q_1$ confines it to the same fan wedge, so the two radial sides cannot
be crossed. The remaining side $aP$ is protected by the same uncut-vertex
separation. Thus $V_1\subset T$ too. The two copied cut edges at $a$ have
the positive curvature gap $\kappa_a$, so its apex $M$ is not on $aP$;
it is strictly inside $T$.

Let $a=0$ and $e=M/|M|$. Since $|M|=|P|=s$, the functional $e\cdot z$
takes values $s$ at $M$, $0$ at $a$, and $s\cos\kappa_a<s$ at $P$.
The strict interior containment forces $e\cdot p>s$. Hence

$$|ap|^2>|aM|^2+|pM|^2.$$

The angle $aMp$ is obtuse. Because $pM$ is the diagonal of the convex
receiver, its source apex angle $\nu$ includes this angle; therefore
$\nu>\pi/2$ as well. Also the intrinsic diagonal through $Q_1$ has
length $|pM|\ge|pq|$. The original triangle $apq$ consequently has an
obtuse angle at $q$, and the spherical-link bound gives $\kappa_q<\pi$.

Thus taking a pole of curvature at least $\pi$ as **source** makes every
bad extension into a convex receiver short. For two distinct receivers,
this supplies a shorter alternative proof of the earlier large-pole
branch. The general weighted-curvature argument is still useful when
both poles have smaller curvature.

## 3. The whole large-angle branch is safe {#base-cones}

Suppose $\theta\ge\pi$. The two outer petals lie in their cones at
$a,b$. With the preceding orientation, the left cone and the reversed
right cone have direction intervals

$$[\alpha,2\pi-\sigma],\qquad
[\tau,2\pi-\beta].$$

Both lie in the sector

$$S=[\min(\alpha,\tau),\,2\pi-\min(\sigma,\beta)].$$

Its width is at most $\pi$. Indeed each of
$\alpha+\sigma$, $\beta+\tau$ exceeds $\pi$ by the vertex sums;
$\alpha+\beta=\theta\ge\pi$; and $\sigma+\tau>\pi$ was just
proved. Thus the sum of the two minima is at least $\pi$.
The sector excludes the positive base direction.

A point in both petals would give
$b-a=(\text{point}-a)-(\text{point}-b)$. The two summands belong to
the left cone and reversed right cone, so their sum would belong to the
convex sector $S$. The nonzero vector $b-a$ points along the excluded
positive base direction, a contradiction. Boundary equality at
$\theta=\pi$ causes no interior overlap.

This settles the remaining petal pair, hence the entire selected net,
throughout the large-angle branch.

## 4. The small-angle branch has an explicit separator {#case-a}

Now $0<\theta<\pi$. The copied cut rays $aP,bR$ have directions
$\alpha$ and $\pi-\beta$, and meet at a point $X$ above the base.
Write

$$L=|aX|,\quad T=|bX|,\quad s=|aM|=|aP|,\quad t=|bM|=|bR|.$$

The middle apex is strictly inside triangle $abX$: its base angles
$\phi,\psi$ are strictly less than $\alpha,\beta$. The convex function
$z\mapsto |az|+|bz|$ takes value $d$ at the two base endpoints and the
strictly larger value $L+T$ at $X$. Therefore

$$s+t<L+T.$$

At least one copied cut edge is **short**, meaning $s<L$ or $t<T$.

**Wider-apex separator.** Either of the following is sufficient:

$$s\le L\ \text{ and }\ \lambda\le\frac{\pi+\theta}{2},
\qquad
t\le T\ \text{ and }\ \rho\le\frac{\pi+\theta}{2}.$$

In particular, if both outer apex angles satisfy the displayed bound,
the pair is safe. No auxiliary hull or curvature ranking is required.

Here is the planar argument, included to identify its exact hypotheses.
The sum-of-angles condition

$$\lambda+\rho<\pi+\theta$$

is automatic: $\lambda+\nu+\rho$ is only part of the source's face-angle
sum $2\pi-\kappa_q$, whereas $\pi+\theta=2\pi-\nu+K$.
Let $e,f$ be unit vectors at angles $\pi+\alpha$ and $\pi-\beta$.
Then

$$R-P=(s-L)e+(t-T)f.$$

Consider the left short-edge condition. If $\lambda\le\theta$, the
linear functional extracting the $e$ coefficient in the basis $e,f$
is nonnegative on the left apex cone and on the reversed right apex
cone. Its value on $R-P$ is $s-L\le0$. Equality confines any common
points to a supporting line; face interiors are disjoint.

If $\theta<\lambda\le(\pi+\theta)/2$, put $g$ at angle
$\pi+\alpha-\lambda$. Both cones lie counterclockwise of $g$ in a
sector of width $\lambda+\max(\rho-\theta,0)<\pi$.
Writing $A=L-s\ge0$ and $B=t-T<A$ gives

$$\det(g,R-P)=-A\sin\lambda+B\sin(\lambda-\theta)<0.$$

If $B\le0$, strictness follows directly. If $B>0$, use $B<A$ and
$\sin\lambda\ge\sin(\lambda-\theta)$, which follows from the stated
upper bound on $\lambda$. This strictly separates the translated cones.
Reflection proves the right short-edge condition.

This is the local wider-angle argument from the
[n6 shared core](../n6/TIDY_CORE.html), with its sufficient hypotheses
retained explicitly. It does not import the n6 Gauss–Bonnet shortcut.

## 5. Exactly how the seventh vertex changes the identity {#correction}

For the triple $Q_0,Q_1,Q_2$, the extra equator vertex is $u_4$.
Let $A_4$ be the sum of its two **source-face** angles, and $B_4$ the
sum of its two **fan-face** angles. Let $\xi$ be the source-face angle
at $u_0$ in $V_4$, and $\zeta$ that at $u_3$ in $V_3$. Define

$$S=(2\pi-\kappa_{u_0}-2\xi)
 +(2\pi-\kappa_{u_3}-2\zeta)>0.$$

Each summand is strictly positive by the closed spherical-link side bound.
The ordinary triangle sums and total curvature give the exact identities

$$2\pi+K-2\lambda-\nu
=(\kappa_q-\kappa_p+B_4-A_4)+S+\nu+2\rho,$$

$$2\pi+K-2\rho-\nu
=(\kappa_q-\kappa_p+B_4-A_4)+S+\nu+2\lambda.$$

For a direct derivation, the two outside source triangles give
$\xi+\zeta+A_4=2\pi-\nu_3-\nu_4$; the source sum gives
$\lambda+\nu+\rho+\nu_3+\nu_4=2\pi-\kappa_q$; and
$A_4+B_4=2\pi-\kappa_{u_4}$. Substitute these three relations and
$\kappa_q+\kappa_p+K+\kappa_{u_0}+\kappa_{u_3}+\kappa_{u_4}=4\pi$
into $S$. No inequality or numerical approximation is used in this step.

Thus the condition

$$H:=\kappa_q-\kappa_p+B_4-A_4\ge0$$

makes both wider-apex bounds strict and proves the entire selected net
in Case A. The [integer-coefficient checker](bipyramid_receiver_identity.py)
expands both identities for all five cyclic triples and both pole choices:
20 exact identities in 20 independent triangle-angle variables.

This answers part of the insertion question quite concretely. At curvature
zero, when $u_4$ subdivides the old equator edge $u_3u_0$, both $A_4$ and
$B_4$ equal $\pi$. The correction disappears and the n6 paired-pole
identity is recovered. After insertion, the additional term is exactly
the difference between the two corner sums at the new vertex.

The correction changes sign when the poles are exchanged. That alone
does not finish the proof: the same pole must also satisfy the chain's
combined-extension rule, and after a switch the long patch may change.

## 6. What is now proved, and what remains {#remaining}

For the selected opposing-chain candidate:

| Branch | Status |
| --- | --- |
| Both extensions short | Entire net proved by the receiver cones |
| One long extension, $\theta\ge\pi$ | Entire net proved by the base cones |
| One long extension, $\theta<\pi$, and a short cut satisfies the wider apex bound | Entire net proved |
| One long extension, $\theta<\pi$, with $H\ge0$ | Entire net proved by the new identity |
| Applicable auxiliary-octahedron bridge | Entire net proved independently |
| Small-fan pocket | Impossible under the long-extension hypothesis |
| Remaining small-angle configurations | Open: prove the sufficient bound, find another separator, or repair the tree |

Because $\lambda+\rho<\pi+\theta$, both outer angles cannot exceed
their common wider bound. The distance-sum inequality also ensures that
both copied edges cannot be long. Therefore failure of this separator
requires a precise opposing choice: the **only short copied edge** is at
the **only oversized apex angle**. Equality in either sufficient test is
already safe. This is a condition for the test to fail, not proof of overlap.

[Four exact coordinate examples](results/bipyramid-receiver-pairs.json),
with their [replay checker](bipyramid_receiver_pairs.py), check the applications and
independently separate all 45 face pairs of their selected nets. Random
and optimized searches are retained as discovery records; none proves
that the remaining small-angle configurations are impossible.


The angle comparisons themselves use [rational angle intervals](angle_intervals.py):
Machin's identity bounds $\pi$, and an alternating arctangent series after
rational argument reduction bounds each face angle. No floating trigonometric
value enters a proof predicate. The examples include both signs of $H$;
a negative $H$ can still pass the more direct wider-apex test.
