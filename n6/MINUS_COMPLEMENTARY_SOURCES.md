# Minus-edge: complementary sources finish every sharp quadrilateral corner

12 September 2026. Written geometric proof, pending independent review.
No numerical sample or point certificate is a premise of this theorem.

Use A=0, B=1, C=2, D=3, P=4, Q=5, with original quadrilateral ACBD.
The remaining faces are ACP, APQ, ADQ, BDQ, BPQ and BCP.

## The theorem and an explicit two-choice rule

If **C or D has curvature at least pi**, the octahedron-minus-edge has a
nonoverlapping original-edge unfolding. Equality is included.

It is enough to prove the C case. If A or B has curvature at least pi,
the previous high-source theorem already supplies an original-edge tree
at that vertex: every possible fifth edge is original there. Otherwise
both A and B have curvature below pi. Use the following two candidates:

* star(A) plus BC: cuts AC, AD, AP, AQ, BC;
* star(B) plus AC: cuts BC, BD, BP, BQ, AC.

Both have sharp fifth-cut endpoint C and a low-curvature fan (B or A).
The cofacial-star reduction therefore leaves only one opposite-face pair
in each net. These are the whole quadrilateral against APQ in the first,
and the whole quadrilateral against BPQ in the second. Their respective
middle triangles are ADQ and BDQ, with the same middle base DQ.

Set

    K = kappa_D+kappa_Q,
    nu_A = angle(DAQ), nu_B = angle(DBQ),
    theta_A = pi-nu_A+K, theta_B = pi-nu_B+K.

If K>=nu_A or K>=nu_B, take the corresponding source: its residual pair
is Case B and COFACIAL_STAR_REDUCTION.md proves that whole net safe.
Otherwise both are Case A. Choose a source X in {A,B} for which both
outer face angles at X are at most theta_X. The identity below proves
that such a source always exists, with both inequalities strict at at
least one source. The original two-angle Case A cone lemma then proves
its pair safe and completes that same whole original-edge net.

For D sharp, interchange C with D and P with Q throughout.

## Why the two Case A choices cannot both fail

Write q_A,q_B,q_C,q_D for the four angles of ACBD, so

    q_A+q_B+q_C+q_D = 2*pi.

Let mu_A=angle(PAQ), mu_B=angle(PBQ), and let

    tau = angle(APQ)+angle(BPQ) > 0.

The outer angles to check at A are q_A and mu_A; at B they are q_B
and mu_B. Add the angle sums in the four triangles ADQ, BDQ, APQ, BPQ,
and the definition of curvature at D and Q. They give the exact identity

    K+q_D = nu_A+nu_B+mu_A+mu_B+tau.             (1)

All original angles and both curvatures in K are strictly positive.
Because theta_A+theta_B=2*pi-nu_A-nu_B+2*K, equation (1) gives:

    theta_A+theta_B-(q_A+q_B)
        = K+q_C+mu_A+mu_B+tau > 0;

    theta_A+theta_B-(q_A+mu_B)
        = K+q_B+q_C+mu_A+tau > 0;

    theta_A+theta_B-(mu_A+q_B)
        = K+q_A+q_C+mu_B+tau > 0;

    theta_A+theta_B-(mu_A+mu_B)
        = 2*pi+K-q_D+tau > 0.                  (2)

The last expression is positive since q_D<pi. Thus every possible sum
of one outer angle from A and one from B is strictly less than
 theta_A+theta_B. Equivalently,

    max(q_A,mu_A)+max(q_B,mu_B) < theta_A+theta_B.

If both sources failed their two-angle tests, choosing a failing angle
at each would contradict this strict inequality. In fact, at least one
source has max(q_X,mu_X)<theta_X. That source is a strict Case A instance
with both required no-wrap angles, exactly the hypotheses of
CASE_A_CONES.md. The proof applies to the entire convex quadrilateral
because it is contained in the apex cone of its triangular petal.

This does not combine pieces of two different successful nets. It proves
that one of the two specified trees has its own residual pair safe; its
other obligations have already been proved for that same tree.

## Boundary and scope audit

* C curvature equal to pi is covered by the sharp-slit reduction.
* A or B curvature equal to pi goes to the already-proved high-source branch.
* K=nu_X goes to Case B. Only strict Case A uses (2).
* No tie-breaker, generic position, or nonflat auxiliary diagonal is assumed.
* All final cuts are original edges and the original quadrilateral stays whole.
* Ordinary boundary contact is allowed; the claim excludes face-interior overlap.

Together with the previous theorems this covers every minus-edge family
with at least two sharp vertices: the former outstanding pairs {C,P}
and {D,Q} are now covered too. Four of the six singleton sharp positions
(A,B,C,D) are covered. The only remaining entire positional families for
this type have **P alone sharp or Q alone sharp**. The all-at-most-pi
family is already proved. This is not yet the full minus-edge theorem.


## Generalization needed for the last singleton family

The two-source argument also works if A and B are both below pi and

    kappa_C+kappa_A >= pi,   kappa_C+kappa_B >= pi.

C itself need not be sharp. Each candidate then satisfies the curvature-gate
extension of COFACIAL_STAR_REDUCTION.md: its low fan and slit-plus-fan
sum supply every non-Case-A premise. The same identity (1), all four
strict inequalities (2), and the Case B alternative are unchanged.
Thus one of star(A)+BC and star(B)+AC is a whole original-edge unfolding.
The sharp-C theorem is a corollary of this more general statement.

The later MINUS_EDGE_PROOF.md uses this generalization to close P-alone
and Q-alone too. The preceding two-pattern count records the intermediate
sharp-corner checkpoint, not the final status of the whole type.
