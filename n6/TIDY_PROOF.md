# A streamlined proof of original-edge unfoldability through six vertices

12 September 2026. **Separate streamlined research manuscript.**
The original notes, alternatives, failures, figures and certificates are
preserved. This is a shorter presentation under self-audit, not independent
review or formal verification. Numerical experiments are not proof premises.

## Scope and structure

The claim concerns full-dimensional convex polytopes with at most six
genuine vertices. Only original edges may be cut; face interiors must be
disjoint, while net-boundary contact is allowed. The argument below uses
one geometric core, a paired-pole rule, and two prism switches. All
geometric details of the new common criterion and planar separators are
collected in [TIDY_CORE.md](TIDY_CORE.md). The longer original dependency
map remains [N6_PROOF_MAP.md](N6_PROOF_MAP.md).

## A short classification, without a computer enumeration

The graph of a convex three-dimensional polytope is simple, planar and
3-connected; every vertex has degree at least three. If some vertex is
adjacent to every other vertex, cut its original edge star. Each edge is
a shortest surface path, since it attains the Euclidean distance of its
endpoints. The shortest-path star theorem gives a nonoverlapping net.
The theorem includes a source at a vertex; see Definition 1 and Theorem 4
of [Kiazyk and Lubiw, SoCG 2015](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SOCG.2015.390).

For four vertices this always applies. For five, absence of degree four
would make all five degrees three, contradicting the even degree sum.
Now take six vertices without a degree-five vertex. In the complement H
of its graph, every degree is one or two. Thus each component is a path
P_j with j>=2 or a cycle C_j with j>=3. The partitions of six give just:

| Complement H | Original graph / exclusion |
| --- | --- |
| P_2+P_2+P_2 | Octahedron |
| P_4+P_2 | Octahedron minus one edge |
| P_6 | Prism with one diagonal |
| C_6 | Triangular prism |
| P_3+P_3, C_3+P_3, C_3+C_3 | All nine edges between the two triples are in the original graph: a K_(3,3), contradicting planarity |
| C_4+P_2 | Removing the two P_2 vertices leaves two disjoint edges: a contradiction to 3-connectivity |

The four retained graphs have the usual original facet structures, which
are unique for a 3-connected planar graph. This also identifies directly
the face lists used below. The triangular-prism graph is a dome: any one
of its quadrilaterals shares an edge with every other facet. The established
dome unfolding theorem applies without requiring parallel metric bases;
see [Pinciu, Corollary 2](https://cccg.ca/proceedings/2007/01a4.pdf), or
the earlier “Domes” treatment in [O'Rourke's author manuscript](https://www.science.smith.edu/~jorourke/Papers/PolyUnf0.pdf).
Only the other three graphs need the new argument. The existing seven-type
computer enumeration is retained as a separate check, not a proof premise.

## The shared core and an original-face comparison

Write kappa_x for vertex curvature, with 0<kappa_x<2*pi and total 4*pi.
Complete the three remaining graphs to an octahedron using uncut flat
quadrilateral diagonals. The shared core proves local separation, the
finite-cut obstruction, opposite-petal cone and pocket lemmas, and the
four final boundary checks. The new paired-pole identity organizes these
into the short octahedron and minus-edge rule below.

The prism also needs an original-face comparison and the cofacial gate.
These keep the final cuts on original edges and leave only a stated
Case A pair to settle at each candidate.

We also use a useful comparison. Let an original degree-four source v
and its sole nonneighbor w be opposite corners of an original quadrilateral
Q with other corners c,d. In the shortest-path star at v, the fifth path
is the straight face diagonal vw. Splitting Q along it gives two leaves
attached along wc and wd. Remove them. In star(v)+wc, removing the single
leaf Q leaves exactly the same uncut tree of other faces, in the same
relative planar positions. Therefore every pair outside Q is safe.

Under **kappa_w<=pi and kappa_c+kappa_w>=pi**, the common cofacial gate
proves all non-Case-A obligations at this same slit. One opposite-petal
pair is already safe by the star comparison. Only the other pair's Case A
remains. Here are the middle bases for that remaining triple:

| Original type | Source / fifth endpoint | Middle base |
| --- | --- | --- |
| Prism diagonal | 1 / 2, 1 / 4, 3 / 0, 3 / 5 | respectively 34, 02, 45, 01 |

If its base-curvature sum is at least its middle apex angle, it is Case B
and the whole candidate is safe. Otherwise the Case A separators in
TIDY_CORE.md apply to the full original outer-face apex cones. The comparison
uses only star nonoverlap; it does not assume an empty infinite exterior
wedge, a stronger claim that is false.

## One paired-pole rule settles the octahedron and minus-edge graph

The final review gives a shorter theorem: **fix any opposite pair, use its
sharper endpoint as source, and put the fifth cut at an equator maximum**.
The complete deduction is in [PAIRED_POLE_RULE.md](PAIRED_POLE_RULE.md).
Its central identity makes the two wider Case A bounds automatic from
kappa_v>=kappa_w; the shared core then excludes every remaining pair.
No comparison between different pole pairs or trial unfolding is needed.

For the minus graph, use facets ACBD, ACP, APQ, ADQ, BDQ, BPQ, BCP and
add CD as an uncut flat hinge. Both A and B have degree four. Choose the
sharper of A,B as v and the other as w, then take a largest-curvature c
among C,D,P,Q. All four star edges and wc are original, and CD remains
uncut. The paired-pole theorem gives the whole net, including equality.

Thus this type needs no source-switch exhaustion. The previous one-identity
switch, its full case analysis and its wider uses are retained in
[the preceding complete review draft](TIDY_PROOF_BEFORE_PAIRED.md) and
MINUS_COMPLEMENTARY_SOURCES.md. The separate two-fixed-tree conjecture
remains an optional question.

## Prism: one fixed fallback with two views

Use original faces

    A=021, B=0352, C=013, D=1254, E=143, F=345,

and let X_i denote the full corner angle of original face X at vertex i.
Add 05 and 24 only as uncut auxiliary hinges when using the common rule.
The four cofacial near-stars we retain are star(1)+25, star(1)+54,
star(3)+20, and star(3)+25. The fifth candidate is

    T={02,12,25,35,45}.

T's uncut adjacencies are C-A, C-B, C-E, E-D, E-F. Every pair except
A/F and B/D has a common uncut vertex. To settle A/F, compare with the
shortest-path star at vertex 2, cutting 20,21,25 and the straight original
face diagonals 23 in B and 24 in D. The four split quadrilateral triangles
are leaves. Removing them leaves the chain A-C-E-F, with exactly T's
uncut hinges. Thus A/F is safe as well. **Only B/D remains in T.**

View B/D around cap A, with base 01 and copied apex 2, or around cap F,
with base 34 and copied apex 5. Their intervening central angle sums are

    Sigma_A=pi-C_3+E_1, Sigma_F=pi-E_1+C_3,
    Sigma_A+Sigma_F=2*pi.

At least one view has Sigma>=pi. In that view either Case A's apex-cone
criterion or Case B's base-cone criterion suffices. Hence **if both views'
Case A branches are safe, T is safe**. It is enough for a view's Case A
to be impossible. The actual convex quadrilaterals lie in the full apex
cones, and their copied lengths are original edge lengths.

In either view the wider Case A lemma's extra angle-sum premise is automatic:
the two outer angles plus the middle angle equal the source's incident
angle sum. Two simple sufficient ways to settle its Case A are therefore:
a nonobtuse middle angle; or both outer apex angles <=(pi+theta)/2.
A source curvature >=pi gives the original, narrower bounds as well.

There is now a shorter way to organize every shape. Let C_A and C_F be
the curvature sums of the three vertices of the two triangular caps, so
C_A+C_F=4*pi. **If both cap sums are at least pi, T works.** Indeed,
in either view lambda+rho+nu=2*pi-kappa_p because its source has degree
three. Hence

    2*lambda+nu-2*pi-K = lambda-rho-C,

where C is that cap's curvature sum. Since 0<lambda,rho<pi, C>=pi
makes this expression and its reflection strictly negative. Both wider
Case A bounds hold, and the two-view observation settles T. In particular
this covers every prism with all curvatures at most pi, since the other
cap can sum to at most 3*pi. The [cap rule](PRISM_CAP_RULE.md) records
the full statement, including equality and its exact example checks.

### Switch 1: a sharp vertex at 2 or 5

If both curvatures are at least pi, both views' Case A branches are safe,
and T works. Otherwise reflect so kappa_2>=pi and kappa_5<pi. Compare
N=star(1)+25 with T. The cofacial gate applies to N; only C/D's Case A
can remain, with middle E, source 1, K=kappa_3+kappa_4, and
theta_1=pi-E_1+K. If K>=E_1, N is safe. In Case A it is also safe if
E_1<=pi/2 or both C_1,D_1<=(pi+theta_1)/2.

To handle the remaining alternative, define

    f_C=2*C_1+E_1-2*pi-K, f_D=2*D_1+E_1-2*pi-K,
    g_B=2*B_5+F_5-2*pi-K, g_D=2*D_5+F_5-2*pi-K,
    L_Xi=(2*pi-kappa_i)-2*X_i>0.

The positivity of L_Xi is the strict spherical-link bound. The original
face-angle sums give the following identities, with ordinary parentheses
pi-X_i denoting positive corner-angle deficits:

    -f_C = C_0+F_5+(pi-B_3)+(pi-C_1)+(pi-D_4),

    -f_D-g_D = 2*D_2+E_1+F_5+2*(pi-B_3)+2*(pi-C_3),

    -f_D-g_B = L_A0+L_A2+L_B5+kappa_1+2*C_1
               +(pi-B_3)+(pi-C_3)+(pi-D_4)+2*(E_1-pi/2).

These shorter forms preserve the older identities in PRISM_SHARP_FAN_SWITCH.md.
The first gives f_C<0. If N has not passed its tests, E_1>pi/2 and f_D>0.
The other two identities then give g_B,g_D<0. These are exactly the two
wider outer-angle bounds for the upper F view of T whenever it is Case A.
The lower A view's Case A is already safe because kappa_2>=pi. The
two-view observation therefore makes T safe. This completes the switch.

### Switch 2: two curvature gates

Suppose

    kappa_2<=pi, kappa_0+kappa_2>=pi, kappa_0+kappa_1>=pi.

Compare M=star(3)+20 with T. The first two premises are M's cofacial
gate. Its residual pair B/E has middle angle F_3, so M is safe whenever
F_3<=pi/2: Case B is already safe, and Case A has a nonobtuse middle.
T is safe whenever F_5<=pi/2: its upper view then has a safe Case A,
while the lower view cannot be Case A since kappa_0+kappa_1>=pi>A_2.
The two-view observation finishes T. At least one of F_3,F_5 is
nonobtuse because they are angles of the same triangle. Thus M or T works.
Reflection exchanges 0 with 4, 1 with 3, and 2 with 5; it fixes T and
permutes the four cofacial near-stars.

### Why five candidates suffice, with at most two for each shape

If both cap sums are at least pi, use T. Otherwise exactly one is below
pi and the other is above 3*pi. Reflect so C_A>3*pi and C_F<pi;
in particular kappa_5<pi. If kappa_2>=pi, Switch 1 supplies
star(1)+25 or T. If kappa_2<pi, then

    kappa_0+kappa_2=C_A-kappa_1>pi,
    kappa_0+kappa_1=C_A-kappa_2>2*pi.

Thus Switch 2 supplies star(3)+20 or T. The reflected orientation
supplies star(3)+25 or star(1)+54, together with T. These are precisely
the five stated original-edge candidates. On each particular shape,
the cap sums and the indicated end curvature select just one or two.

These cases exhaust every curvature assignment; neither auxiliary
diagonal is cut. Thus the prism-with-diagonal type, and with it every case
through six vertices, has the stated written existence argument. The
earlier seven-candidate proof remains correct and is preserved in
[the first review draft](TIDY_PROOF_FIRST_REVIEW.md) and PRISM_EDGE_PROOF.md.
Five is a sufficient family size, not a claim of minimality.

### Selecting one tree without a trial unfolding

The proof gives an explicit rule, not just a list to search. If both cap
sums are at least pi, choose T. Otherwise reflect to C_A>3*pi and C_F<pi.
For kappa_2<pi, choose star(3)+20 when F_3<=pi/2 and T otherwise.
For kappa_2>=pi, put K=kappa_3+kappa_4 and choose star(1)+25 if

    K>=E_1, or E_1<=pi/2, or 2*D_1+E_1<=2*pi+K.

If none holds, choose T. The first two tests are Case B and nonobtuse
middle; in strict Case A the last is the D_1 wider bound, while the
C_1 bound holds automatically by the first switching identity. The two
other identities prove T safe when all three closed tests fail. Undo
the reflection to obtain the original labels. Thus curvature and original
face angles select one successful cut tree without comparing planar nets.

## Equalities, preservation, and review status

All comparison equalities enter proved closed cases: source or fan curvature
pi, the slit threshold, a middle Case A/B boundary, a right middle angle,
and an outer wider-angle threshold. Only failed closed tests are added as
strict inequalities. Positive curvature at genuine vertices supplies the
strictness used elsewhere. No perturbation of a flat face lattice, unique
maximum, or uniform positive clearance is assumed.

The stronger every-slit Lemma F and original Triple Lemma are not premises
of this existence proof. Their statements and unresolved work remain in
the old notes, alongside failed rules, examples, certificates and figures.
Nothing has been discarded to obtain this shorter exposition.

This manuscript is a reconstructed research proof under self-audit.
Independent mathematical review and formal verification remain outstanding.
The accompanying exact algebra and finite-graph checks do not formally
verify the geometric arguments, and metric samples do not prove them.
