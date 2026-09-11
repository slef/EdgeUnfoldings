# A middle-patch switch for three inward corners with a common direction

**Subsequent completion, 11 September:** [the equal-length argument](LEMMA_F_CHORD.md)
completes the selected H/R octahedron proof. Earlier open-case counts in this
note describe the investigation at that stage. The every-slit Lemma F and
full n=6 theorem remain open; the new research proof awaits independent review.


10 September 2026 JST / 9 September UTC. **Written geometric proofs for
explicit subfamilies; the full octahedron remains open.** These results
extend [OCTA_PATCH_BUDGET.md](OCTA_PATCH_BUDGET.md). They allow exchanging
the two poles and do not prove the fixed sharpest-source rule.

## A simple condition and a four-tree rule

Choose opposite vertices v,w, with one globally sharpest (H). Flatten the
four two-face patches. Suppose three consecutive patches lean in the same
direction. By rotation and reflection, label them Q0,Q1,Q2, all forward,
with Q3 convex. Their inward corners are u1,u2,u3, respectively.

The **middle patch** is Q1. Its reflex excess is

    rho_1 = (the inward angle of Q1 at u2) - pi.

Curvature kappa_x means the angle deficit at an original vertex x.

**Simple middle-patch theorem.** If

    rho_1 <= min(kappa_v, kappa_w),

one of four prescribed original-edge nets is nonoverlapping. Use either
pole as the center of the uncut fan, and either u2 or u3 as the endpoint
of the fifth cut. Explicitly, try

    star(v) + w-u2,    star(v) + w-u3,
    star(w) + v-u2,    star(w) + v-u3.

Here star(v) means cutting all four original edges incident to v. This is
an existence theorem for every octahedron satisfying the condition, not
an extrapolation from sampled examples.

For three backward patches Q_i,Q_(i+1),Q_(i+2), the reflected prescription
uses the physical endpoints u_i,u_(i+1). In both directions the middle
patch is Q_(i+1). Exchanging poles retains the physical fifth-edge endpoint.

**Curvature-only corollary.** It is enough that

    min(kappa_v, kappa_w) + kappa_(u2) >= pi.

Indeed the other patch angle e_2>0 at the middle inward vertex gives
rho_1=pi-kappa_(u2)-e_2 < pi-kappa_(u2). The corollary follows from the
simple condition. This is a sufficient condition; its failure implies
nothing about whether an unfolding exists.

## The stronger switch theorem

As in the budget proof, write theta_i^p for the original face angle of
Q_i at pole p, and l_i^p for the patch's extra angular extension at that
pole. A convex patch has extension zero. The two views obey

    l_i^v + l_i^w = rho_i,
    0 < l_i^p < pi for i=0,1,2.

The first inward vertex in the forward chain is u1. The following weaker
hypotheses also suffice for the same four trees:

    l_1^v <= kappa_v,    l_1^w <= kappa_w,
    rho_1 <= kappa_(u1) + min(kappa_v, kappa_w).

These inequalities constitute the **switch theorem**. The simple theorem
is its corollary: each middle extension is strictly smaller than rho_1,
and kappa_(u1)>0. The switch theorem can therefore apply when the total
middle excess exceeds the smaller pole curvature. The saved `switch`
example does exactly that, with exact rational interval checks.

## Why the four-tree rule works

The proof uses the six sufficient whole-patch wedge inequalities from
[OCTA_HALF_FAN.md](OCTA_HALF_FAN.md). Substituting FFF and the two selected
openings leaves these conditions at a fan pole p:

| Fifth-edge endpoint | Conditions sufficient for the entire net |
| --- | --- |
| u2 | l_2^p <= theta_3^p; l_0^p <= theta_1^p+kappa_p; l_1^p <= kappa_p |
| u3 | l_0^p <= theta_1^p; l_1^p <= theta_2^p+kappa_p; l_2^p <= kappa_p |

All omitted inequalities have zero left sides or are weaker than these.
The same table in the original physical patch indices applies after
exchanging poles: the ring reverses and forward becomes backward. These
are sufficient tests for every face pair, including the cut-side fan faces.
They do not use the refuted conditional far-fan reduction.

By the [shared-budget argument under H](OCTA_PATCH_BUDGET.md), choose a
pole p such that all three individual extensions are below its fan gap:

    l_i^p < kappa_p,       i=0,1,2.

If a pole has curvature at least pi, that pole works. Otherwise all six
curvatures are below pi, and the total lean budget supplies such a pole.

If l_2^p<=theta_3^p, the u2 row is satisfied. If l_0^p<=theta_1^p, the u3
row is satisfied. It remains to consider

    l_2^p > theta_3^p,    l_0^p > theta_1^p.

Let q denote the other pole, not an equator endpoint. The last bad patch
is followed by the convex Q3, so the endpoint identity is

    rho_2 - (theta_3^p+theta_3^q)
       = f_3-pi-kappa_(u3) < 0.

Together with l_2^p+l_2^q=rho_2, this implies

    l_2^q < theta_3^q.

Thus the last patch fits at the other pole. For the first patch, the
following patch Q1 is bad, and the corresponding identity carries its
reflex excess:

    rho_0 - (theta_1^p+theta_1^q) = rho_1-kappa_(u1).

For completeness, f_0+e_1=2*pi-kappa_(u1),
theta_1^p+theta_1^q+e_1+f_1=2*pi, and f_1=pi+rho_1 give this identity.
Subtracting the strictly positive excess l_0^p-theta_1^p yields

    l_0^q-theta_1^q
       = rho_1-kappa_(u1) - (l_0^p-theta_1^p)
       < rho_1-kappa_(u1) <= kappa_q.

The middle extension l_1^q<=kappa_q is the remaining switch hypothesis.
All three conditions in the u2 row now hold at q. This proves the switch
theorem, and therefore the simple theorem and curvature-only corollary.
Equality in the nonstrict hypotheses is included. Boundary contact in a
net is allowed; positive-area overlap is excluded.

## What is still missing

The original common-direction three-patch family is only **partly settled**.
The switch theorem leaves two disjoint possibilities outside its hypotheses:

1. The middle patch extends farther than the fan gap at at least one pole.
2. Both middle extensions fit their gaps, but
   rho_1 > kappa_(u1)+min(kappa_v,kappa_w).

The first possibility is nonempty: `three-chain-uncovered` is an exact
example. Its middle extension at one pole strictly exceeds that pole's gap.
Its chosen net is nevertheless separately certified safe. This is a limit
of the sufficient condition, not an unfolding counterexample. No geometric
example is asserted here for the second possibility; whether additional
geometry excludes it is a separate proof target.

The next step is to use actual radial positions when the middle cone
crosses its gap, or to show that a different opposite pair falls in an
already proved family. Angle sums and the shared-excess identities alone
have not completed that step. Numerical optimization and linear relaxations
used during discovery are not premises of any theorem above.

The coarse patch count remains **four of five entire regimes proved**, with
the fifth now containing both the mixed-direction theorem and these new
common-direction subfamilies. It is not a completion percentage. The
fixed sharpest-source analysis remains **49 classes: 2 excluded, 47 open**.
Neither the full octahedron nor the full n=6 theorem is claimed proved.

## Exact illustrations and replay

- `three-chain-simple` satisfies the simple excess inequality.
- `three-chain-switch` satisfies the stronger theorem's hypotheses but
  strictly fails the simple inequality at the smaller-curvature pole.
- `three-chain-family` allows all 18 coordinates of the switch example to
  vary independently by 1/100 in either direction. The same tree passes the
  theorem tests and all 28 independent face-pair checks throughout.
- `three-chain-uncovered` fails the middle-gap hypothesis, yet its selected
  net passes all 28 independent checks. Its coordinates come from the
  earlier `sector-three-patch-radial-failure` example.

Both positive examples and the whole coordinate box also exactly fail the
older sharper-pole weighted-curvature condition for all three opposite
pairs. This distinguishes the new result from that criterion; other
previous sufficient theorems may overlap these families.

All commands below use only the Python standard library:

```sh
python3 -m n6.three_chain n6/results/three-chain-simple.certificate.json
python3 -m n6.three_chain n6/results/three-chain-switch.certificate.json
python3 -m n6.three_chain n6/results/three-chain-family.certificate.json
python3 -m n6.three_chain n6/results/three-chain-uncovered.certificate.json --analyze
python3 -m n6.polycert verify n6/results/three-chain-family.certificate.json --bits 240
python3 -m n6.three_chain_examples
```

The last command rebuilds the point and box certificates, the independent
net reports, and the exact audit of the older weighted-curvature criterion.
It does not run the numerical search that suggested the examples. Decimal
angles in figures are illustrations; the certificates use outward rational
bounds at 240 fractional bits.

## Subsequent connection to Lemma L

[LEMMA_L_CURVATURE_GATE.md](LEMMA_L_CURVATURE_GATE.md) proves a complementary
local result. In a three-common-direction chain, slit at the equator vertex
with no inward corner. If its curvature plus the fan pole curvature is at
most pi, the first and last patches have disjoint angular cones. All three
local pairs are then safe, even when the middle-patch conditions above fail.

The exact `three-chain-uncovered` solid satisfies this at its maximum-curvature
equator vertex u3. See `local-gate-three-chain.certificate.json` for this
alternative cut and its separate whole-net certificate. The local theorem
alone does not settle the opposite-petal and far-fan pairs, so neither of
the two general remaining branches above has been closed.
