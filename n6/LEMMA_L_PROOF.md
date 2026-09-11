# Lemma L: proof for the maximum-curvature slit

11 September 2026 JST. **Lemma L is proved below.** This is a geometric
proof; numerical searches and individual certificates are not premises.
On its own it does not prove Lemma F or the whole net. The subsequent
[equal-length completion](LEMMA_F_CHORD.md) supplies the selected octahedron
result; the stronger every-slit Lemma F and full n=6 remain open.

## The theorem

Let v,w be opposite vertices of a nondegenerate convex octahedron, with

    kappa_v >= kappa_w.

Choose u of maximum curvature among the four equator vertices. Cut the
four edges at v and the edge wu. Then the first and last petals do not
overlap each other or the fan face at the opposite side of the slit.
These are exactly the three local pairs in Lemma L.

In particular this proves the stated Lemma L when v is globally sharpest.
The weaker comparison of the two poles already suffices. A different slit
after a switching operation need not satisfy the equator-maximum condition;
the theorem must not be reused there without checking its hypotheses.

We first prove that the two flank patches cannot meet through the intervening
fan. This is the missing step above the 180-degree curvature threshold.
The earlier cut-edge argument then deals with possible entry across the slit.

## 1. A spherical-link bound at a convex vertex

At a vertex p, intersect its tangent cone with the unit sphere centered at p.
The result is a geodesically convex spherical polygon contained in an open
hemisphere. Its vertices are the directions of the edges at p. Its sides
have lengths equal to the face angles at p, so its perimeter is

    Gamma_p = 2*pi-kappa_p.

The direction of a vertex q not adjacent to p lies strictly inside this
polygon: q is strictly inside each face-support half-space through p.

Let a be one edge direction and b this interior direction. The great-circle
ray from a through b exits the polygon at c. The arc a-c has length less
than pi (the polygon is contained in an open hemisphere), and

    distance(a,c) > distance(a,b).

The two polygon-boundary paths from a to c each have length at least the
shortest spherical distance a-c. Therefore

    Gamma_p > 2*distance(a,b).                         (1)

There is a useful one-sided version. Remove either polygon side incident
to a. The remaining boundary path still contains c, since the interior ray
cannot exit along a side incident to its starting vertex. If the removed
side has length omega, then

    Gamma_p-omega > distance(a,b).                    (2)

These arguments also prove the ordinary cone inequality
omega<=Gamma_p/2 for any single face angle omega: the other boundary path
between that side's endpoints cannot be shorter than their spherical
distance, which is omega<pi.

## 2. What flattening a flank patch does to its pole angle

Write

    r=|wu|,  s=|vu|,  D=|wv|,
    alpha=angle(uwv),  beta=angle(uvw).

Suppose one flank patch has its inward corner *away* from the slit u.
Its corner e at u is then strictly between 0 and pi. Flatten this patch.
It is contained in the outer triangle with vertices w,u,P, where P is the
developed copy of v; its other equator vertex is the reflex vertex inside
that triangle. Put t=|wP| and let gamma be its angle at w. Thus gamma is
exactly that flank's fan angle plus its extension toward the fan interior.

The original angle angle(wuv) is at most e, by the triangle inequality
for directions on the unit sphere centered at u: insert the direction of
the other equator vertex between the directions toward w and v. Because
e<pi, the cosine law gives

    t >= D.

For fixed r,s, the angle at w satisfies

    cos(gamma(t)) = (r*r+t*t-s*s)/(2*r*t).

If beta<=pi/2, the cosine law at v says D*D+s*s-r*r>=0. Consequently

    cos(gamma(t))-cos(gamma(D))
      = (t-D)*(t*D-r*r+s*s)/(2*r*t*D) >= 0,

and hence

    gamma <= alpha.                                  (3)

All denominators are positive. The original and flattened triangles are
nondegenerate, and the equality beta=pi/2 is included.

There is a second bound for the complementary case. If beta>pi/2, then
r*r>D*D+s*s, so r>s. For every permissible t>0 the numerator
r*r+t*t-s*s is positive. Therefore

    gamma < pi/2.                                    (4)

Both flank patches use the same original triangle wuv, so the same beta
case applies to both.

## 3. The through-fan route is impossible

Number the fan W0,W1,W2,W3 from the slit. Let omega_i be their angles at w,
and Gamma=omega_0+omega_1+omega_2+omega_3=2*pi-kappa_w.
The possible inward extensions toward the intervening fan are F0 for the
first patch and B3 for the last. Their angular ranges do not overlap by
this route if

    F0+B3 <= omega_1+omega_2.                          (5)

If neither extension exists, (5) is immediate.

**Case beta<=pi/2.** If only the first patch extends, its complete outer
angle gamma_0=omega_0+F0 is at most alpha by (3). Apply (2) at w to the
edge direction wu and interior direction wv, omitting the final fan face:

    gamma_0 <= alpha < Gamma-omega_3.

This is (5), strictly. The last-only case uses the reflected boundary path.
If both extend, (1) and (3) give

    (omega_0+F0)+(omega_3+B3) <= 2*alpha < Gamma,

again giving (5), strictly.

**Case beta>pi/2.** Apply (1) at v instead, with edge direction vu and
interior direction vw. It gives Gamma_v>2*beta>pi, and so kappa_v<pi.
Our hypothesis kappa_v>=kappa_w then implies kappa_w<pi, hence Gamma>pi.
The acute-angle bound (4) applies to each extending patch. If both extend,

    (omega_0+F0)+(omega_3+B3) < pi < Gamma.

If only the first extends, the cone inequality at w gives

    Gamma-omega_3 >= Gamma/2 > pi/2 > gamma_0.

The last-only case is reflected. Thus (5) holds in all cases.

This entire through-fan proof requires only the pole curvature comparison,
not the maximum-curvature slit rule. More generally, it works whenever the
source pole has curvature at least pi or the fan pole has curvature at
most pi; the pole comparison ensures at least one of those alternatives.

## 4. The across-slit route is harmless under the slit rule

The [curvature-gate proof](LEMMA_L_CURVATURE_GATE.md) excludes this route
when kappa_u+kappa_w>=pi. Together with (5), this now settles that entire
curvature branch, including equality.

When kappa_u+kappa_w<pi, use the complete
[cut-edge proof](LEMMA_L_SMALL_SUM.md). Here is its remaining argument,
so that the dependencies are explicit. At most one flank is inward at u.
If its extension B does not exceed kappa_w, angular interiors are disjoint.
Otherwise, reflect to make it the first patch and put rho=e-pi. Then

    kappa_w < B < rho < pi-kappa_u.

The slit rule and Gauss--Bonnet give

    4*kappa_u >= 4*pi-kappa_v-kappa_w > 2*pi-kappa_w,

so 2*kappa_u+kappa_w>pi. Put w=(0,0), A=(r,0) for the first u, and
A'=r*(cos(kappa_w),-sin(kappa_w)) for the other u. The inward petal's cut
edge is directed by d=(cos(rho),-sin(rho)). Its third vertex lies left of
the oriented line through A in direction d. Meanwhile

    det(d,A'-A) = -2*r*sin(kappa_w/2)*cos(rho-kappa_w/2) < 0,

since 0<rho-kappa_w/2<pi/2. Thus A' lies strictly right. All directions
from A' into the entire opposite patch lie in the relative-angle interval

    [rho-pi-kappa_w, -(kappa_u+kappa_w)] subset (-pi,0).

Its two whole faces stay strictly to the right of the same line. This
separates the inward petal from both the opposite fan face and the opposite
petal. The other mixed pair has no across-slit extension, and (5) excludes
the other route. All three local pairs are safe.

This completes Lemma L for every curvature sum, including all boundaries
and straight patch corners.

## 5. Strict separation from the opposite finite slit edge

The closed first petal V_0 does not meet the closed opposite finite slit
edge wb, where b is the last copy of u_0. Reflection gives the last-petal
version. This stronger boundary fact is useful when removing the first
patch from the closed curve in the later Lemma F reduction.

The through-fan bounds above put V_0 strictly before the last radial
direction when approached through the fan: its forward angular endpoint
is at most omega_0+F_0<Gamma. Across the gap, B_0<kappa_w gives strict
angular separation. The point w itself is outside V_0 by their common
equator line.

It remains to treat B_0>=kappa_w. The first patch is inward at its slit
copy A; put rho=angle_A(Q_0)-pi. The small outer triangle gives

    rho>B_0>=kappa_w,   rho<pi-kappa_u.

Thus the same cut-edge separator from Section 4 applies even when
B_0=kappa_w: its proof required rho>kappa_w, which is still strict.
Both w and b lie strictly to the right of line A->P, since

    det(d,w-A) = -r*sin(rho) < 0,
    det(d,b-A) = -2*r*sin(kappa_w/2)*cos(rho-kappa_w/2) < 0.

Their whole closed segment lies strictly to the right. The entire closed
petal V_0 lies to the left or on that line, so even boundary contact is
excluded. This covers equality of the angular extension with the gap;
it does not exclude boundary contacts in unrelated parts of a net.

## Scope at the Lemma L stage (retained history)

- **Lemma L: 3/3 local pair statements proved** under its stated selections.
- The theorem applies to ties in either curvature selection.
- It concerns positive-area overlap; ordinary shared boundary points or
  edges do not count as overlap.
- With the 19 shared-vertex pairs, **22/28 pairs of this selected net**
  are now universally safe.
- The two opposite-petal and four petal-versus-far-fan pairs remain the
  separate Lemma F problem. The surviving interior-fan reduction removes
  two of the latter after opposite-petal safety is established.
- The full octahedron and n=6 remain unproved. In particular the chosen
  maximum-curvature slit need not be one of the angle-safe openings from
  the earlier switching theorem. Combining different successful partial
  choices would not prove a single whole net works.
- The previously audited 49-class enumeration for all four openings has
  not been recounted here. Its recorded 2 excluded / 47 open count is a
  separate conservative measure, not the status of Lemma L.

## Exact illustrations and replay

The large-sum example and the 18-coordinate radial family independently pass
the geometric hypotheses and full-net checks. A further integer-coordinate
example has an obtuse angle beta and satisfies the weaker pole comparison,
but its source is not globally sharpest. It illustrates the broader theorem;
it must not be advertised as an example of the stronger H hypothesis.

```sh
python3 -m n6.local_lemma n6/results/local-gate-away.certificate.json
python3 -m n6.local_lemma n6/results/local-gate-radial-family.certificate.json
python3 -m n6.local_lemma n6/results/lemma-L-obtuse.certificate.json
python3 -m n6.local_lemma_examples
```

These exact checks illustrate and audit the implementation. The universal
result follows from Sections 1–4, not from the number of checked examples.
