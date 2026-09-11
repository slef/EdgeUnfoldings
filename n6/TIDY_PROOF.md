# A streamlined proof of original-edge unfoldability through six vertices

12 September 2026. **Separate draft in progress during the proof review.**
The original notes, alternatives, failures, figures and certificates are
preserved. This is a shorter presentation under self-audit, not independent
review or formal verification. Numerical experiments are not proof premises.

## Reading map

The intended main proof has three parts: one reusable octahedral unfolding
criterion, one complementary-source identity for the minus-edge type, and
two prism switches. The geometric details are collected separately in
[TIDY_CORE.md](TIDY_CORE.md). Until that reconstruction is complete, the
current dependency map remains [N6_PROOF_MAP.md](N6_PROOF_MAP.md).

## The minus-edge switch in one identity

The original facets are ACBD, ACP, APQ, ADQ, BDQ, BPQ, BCP. Suppose
A and B have curvature below pi and

    kappa_C+kappa_A>=pi,   kappa_C+kappa_B>=pi.

Compare the two original-edge cuts star(A)+BC and star(B)+AC. The
cofacial-star and curvature-gate reduction leaves only ACBD/APQ in the
first candidate and ACBD/BPQ in the second. Each statement concerns the
whole candidate in question; safe pairs are not moved between candidates.

Set K=kappa_D+kappa_Q, nu_A=angle(DAQ), nu_B=angle(DBQ). If K>=nu_X
for either source X, its remaining pair is Case B and that net is safe.
Otherwise theta_X=pi-nu_X+K lies in (0,pi) for both sources.

Let q_X be the quadrilateral angle at X, mu_A=angle(PAQ),
mu_B=angle(PBQ), and tau=angle(APQ)+angle(BPQ)>0. The original face-angle
sums and the two curvatures give

    K+q_D=nu_A+nu_B+mu_A+mu_B+tau,
    q_A+q_B+q_C+q_D=2*pi.

Consequently

    theta_A+theta_B
      = (q_A+mu_A)+(q_B+mu_B)+(K+q_C+tau).

The final parenthesis is positive, so at least one source satisfies
q_X+mu_X<theta_X. Both of its positive outer face angles are then below
theta_X. The Case A cone lemma separates its remaining pair and completes
that entire original-edge net. Reflection gives the corner-D statement.

This short proof replaces the four comparisons in
MINUS_COMPLEMENTARY_SOURCES.md without discarding them. The exhaustive
curvature argument selecting this switch or a direct net will follow here.
