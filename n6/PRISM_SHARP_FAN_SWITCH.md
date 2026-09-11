# Prism: a sharp fan vertex is enough after switching between two nets

**Later completion in the same continuation:** [PRISM_EDGE_PROOF.md](PRISM_EDGE_PROOF.md)
and [MINUS_EDGE_PROOF.md](MINUS_EDGE_PROOF.md) close both whole types as written
research arguments, pending independent review. Any remaining-case count below
records this ingredient's earlier scope. The underlying theorem remains valid.


12 September 2026. Written geometric proof, pending independent review.
All identities below are exact. Numerical experiments are not premises.

Use original faces A=021, B=0352, C=013, D=1254, E=143, F=345.
Write X_i for the full interior angle of original face X at vertex i,
Gamma_i for the incident angle sum, and kappa_i=2*pi-Gamma_i.

## Theorem and two original-edge candidates

Every prism-with-one-diagonal realization with kappa_2>=pi or kappa_5>=pi
has an original-edge unfolding. Equality is included.

If both are sharp, use PRISM_TWO_SHARP_ENDS.md. Otherwise reflect so that
kappa_2>=pi and kappa_5<pi. The two candidates are

    N = star(1)+25 = {01,12,13,14,25},
    T = {02,12,25,35,45}.

The sharp-cut, low-fan cofacial reduction proves every obligation in N
except the pair C/D. Its middle triangle is E, apex 1, middle base 34.
The reference-star reduction PRISM_ONE_PAIR.md proves every obligation in
T except B/D. Neither candidate cuts an auxiliary quadrilateral diagonal.

Put K=kappa_3+kappa_4>0. If K>=E_1, N is Case B and is safe. Otherwise
its residual pair is Case A with theta_1=pi-E_1+K in (0,pi).

The wider Case A theorem CASE_A_WIDE_CONES.md proves N safe if E_1<=pi/2,
or if both outer angles C_1,D_1 are at most (pi+theta_1)/2. The first
condition uses its middle-nonobtuse corollary. The second uses the fact
that at least one cut side is short, so the bound holds on a short side.

We prove that whenever these sufficient choices do not apply, T is safe.

## Three elementary angle identities

For each original corner define the positive link slack

    L_Xi = Gamma_i-2*X_i > 0.

Positivity follows from the strict spherical-link side inequality at a
genuine convex vertex, including flat auxiliary hinges. Also X_i is in
(0,pi), every curvature is positive, and triangular/quadrilateral face
angles sum to pi/2*pi respectively.

Define the signed failures of the wider bounds:

    f_C1=2*C_1+E_1-2*pi-K,
    f_D1=2*D_1+E_1-2*pi-K,
    g_B5=2*B_5+F_5-2*pi-K,
    g_D5=2*D_5+F_5-2*pi-K.

A value <=0 means that outer angle passes its wider bound. Expanding
curvatures and using the six original face-angle sums gives:

    f_C1 + 2*C_0 + L_B3 + L_D4 + E_1 + 2*F_5 = 0;       (1)

    f_D1 + g_D5 + 2*D_2 + 2*E_3 + 2*F_3
         + 2*kappa_3 + E_1 + F_5 = 0;                  (2)

    f_D1 + g_B5 + L_A0 + L_A2 + L_B5
         + 2*C_1 + E_3 + F_3 + (pi-D_4)
         + kappa_1 + kappa_3 + 2*(E_1-pi/2) = 0.      (3)

These are identities of actual original face angles, not a realizability
claim about an arbitrary angle assignment. All terms after f_C1 in (1)
are positive, so f_C1<0 always. Therefore, if N has not already been
proved safe by the preceding tests, necessarily

    E_1>pi/2,    f_D1>0.

Every other term in (2) is positive, so g_D5<0. Under E_1>pi/2, every
other term in (3) is positive too, giving g_B5<0. Thus **both upper-cap
outer angles obey the wider Case A bound strictly**.

## Finish the single remaining pair B/D in T

View B and D around lower cap A, copied apex 2. In Case A, kappa_2>=pi
puts both outer apex angles strictly below pi-A_2, and hence below the
Case A threshold pi-A_2+kappa_0+kappa_1. That view is safe by the original
apex-cone proof.

Otherwise it is Case B. Its intervening central angle sum is

    T_A = pi-C_3+E_1.

If T_A>=pi, the base-cone lemma separates B/D. If T_A<pi, use the upper
cap F instead. Its central angle sum is T_F=2*pi-T_A>pi. The upper
view's Case B is therefore safe by the base-cone lemma. In its Case A,
theta_5=pi-F_5+K is in (0,pi), and g_B5,g_D5<0 proved above say that
both outer apex angles are below (pi+theta_5)/2. The wider apex-cone
lemma therefore separates the same whole quadrilaterals. Its angle-sum
premise is automatic: B_5+D_5=Gamma_5-F_5 is strictly below
2*pi-F_5+K=pi+theta_5, by kappa_5+K>0.

These alternatives exhaust B/D in T. Its other fourteen pairs were already
proved safe, so T is a whole original-edge unfolding. Together with N's
earlier alternatives, this proves the theorem.

## Boundary and dependency audit

* K=E_1 goes to N's Case B; only strict Case A uses theta_1.
* E_1=pi/2 goes to the nonobtuse-middle corollary.
* f_D1=0 passes the closed wider bound at N.
* T_A=pi goes to the closed base-cone lemma.
* Upper-cap Case A is used only with theta_5 in (0,pi).
* Original quadrilaterals lie inside their convex apex cones. The planar
  Case A argument needs equal copied edge lengths and nondegenerate middle
  triangles; it does not require the outer faces themselves to be triangles.
* All final edges in N,T are original. The degree-three reference star
  in PRISM_ONE_PAIR.md is a comparison, not a final cut instruction.

The three identities can be checked by rational linear coefficient
expansion. Their positive terms give the mathematical contradiction;
a numerical optimization or finite sampling result is not required.
The published star theorem, prior planar cone arguments, and this written
proof still merit independent mathematical review.

## Remaining prism scope

Together with the all-low theorem and PRISM_COMPLEMENTARY_ROUTES.md, an
unresolved prism must now have **both kappa_2,kappa_5<pi, their sum below
pi, and some other vertex curvature above pi**. That last regime has not
been claimed solved here.
