# A precise example outside three earlier simple criteria

**Update:** the stronger [local radial-cover theorem](OCTA_RADIAL_COVER.md)
now covers this example and a fifteen-parameter neighborhood. The earlier
criterion failures below remain correct. A new exact example outside the
stronger test is recorded in that theorem’s scope section. The one-patch
whole-net claim also needs correction after [HINGE_AUDIT.md](HINGE_AUDIT.md).

The new geometric theorems do not yet cover every octahedron. This is now
checked on a small integer example, rather than inferred only from a sample:

    v =(  0,  0,  0)     w =(-18,83,19)
    u0=( -4, 47, 17)     u1=( -5,37,10)
    u2=(-58, 70,-29)     u3=(-12,93,34).

The eight original facets are w u_i u_(i+1) and v u_(i+1) u_i, with cyclic
indices. The exact checker establishes all of the following:

- v has maximum curvature, but its four patches have two inward corners, so
  it lies outside the earlier zero/one-patch filter. Only the zero-patch
  whole-net theorem currently survives the hinge audit.
- Every possible sector vertex is either below 120 degrees of curvature,
  or fails the weighted opposite-pole curvature bound.
- At every vertex meeting the 120-degree threshold, there is a strictly
  convex patch whose two incident spokes exceed the pole chord length.
  Therefore the short-edge-cover theorem does not apply either.
- A specified original four-choice net nevertheless has an independent
  all-28-pairs nonoverlap certificate.

Thus this is **not an unfolding counterexample**. It shows exactly why the
three new simple sufficient tests cannot be promoted to a universal proof.
It also does not refute the broader shortest-path sector condition, which
compares against actual surface-path length rather than the Euclidean chord.

```sh
python3 -m n6.proof_family_audit n6/results/octa-new-criteria-uncovered.certificate.json
python3 -m n6.polycert verify n6/results/octa-new-criteria-uncovered.certificate.json --bits 240
```

## Numerical searches are kept separate

The 20,000-shape seed-6090948 pilot counted 10,386 shapes satisfying the
zero/one-patch criterion, 17,487 the weighted curvature-pair criterion, and
19,978 some short-edge-cover criterion. These counts overlap. Sixteen shapes
passed none of the three numerical tests. They are sample classifications,
not proportions of the full shape space and not certificates of those
individual hypotheses. The exact example above is a rounded and independently
verified representative of that unresolved part of the sample.

A separate targeted search covered the 22 then-listed fixed-source failure
classes for 120 seconds each: 7,140 optimizer runs and 3,109,962 objective
evaluations. The reduction to that list was later withdrawn in the hinge audit; the
current original target has 47 open classes. No positive simultaneous-overlap candidate was found. Many best
scores were close to numerical zero. This excludes **no further class** and
provides no universal certificate. Coordinates, bounds, guards, and outcomes
are retained in `results/octa-targeted-session.json`.

## A proved reduction: the remaining curvature is concentrated on a face

This pattern can now be established for every octahedron not covered by the
opposite-pair curvature theorem, without using the far-fan lemma.

**Lemma.** Suppose none of the three opposite pairs satisfies the curvature
theorem. There is a triangular face containing every vertex of curvature at
least 120 degrees. The total curvature of that face is strictly greater than
360 degrees; each of the three vertices outside it has curvature strictly
below 120 degrees.

**Proof.** In each opposite pair label the larger curvature M_i and the
smaller m_i, breaking a tie arbitrarily. Failure of the sufficient theorem
means M_i+2*m_i<360 degrees. Therefore m_i<120 degrees, since M_i>=m_i.
Choose the endpoint with curvature M_i from each pair. In the octahedral
graph, any choice of one endpoint from each of its three opposite pairs is
a triangular face. Every vertex outside this face has curvature m_i<120.
The six curvatures sum to 720 degrees, so the chosen face has curvature
720-(m_1+m_2+m_3)>360 degrees. This proves the claim, including ties.

Since the average curvature is 120 degrees, at least one vertex reaches
that threshold. Thus the uncovered shapes have exactly one of three
patterns:

| Vertices with curvature at least 120 degrees | Their positions |
| --- | --- |
| One | One vertex of the chosen face |
| Two | The endpoints of an edge of that face |
| Three | All three vertices of that face |

These are three exhaustive curvature branches, not three solved cases or
three equal fractions of the problem. They do not replace the 49-class
fixed-source analysis. They narrow the independent sector route: it is
enough to study curvature concentrated around one face. Both saved residual
integer examples are in the three-vertex branch; their examples alone did
not establish this reduction.

The next geometric target is to use the shared face to coordinate the three
sector choices, rather than demanding that each choice pass conservative
local bounds separately. This is a proof target, not yet an unfolding rule
proved for the remaining family.
The full octahedron theorem, the global four-choice rule, and the general
forms of L and F remain open.


## A related literature result, with an extra geometric hypothesis

Radons, *Edge-unfolding nested prismatoids*, Theorem1.1, proves unfoldability
when the solid is the convex hull of polygons in two parallel planes and
one polygon's orthogonal projection is properly contained in the other.
Thus octahedra with two opposite parallel triangular faces and strict
projection containment are already covered by that theorem. Its construction
splits the lateral band into two pieces and uses radial monotonicity.

The curvature-face reduction above does not imply parallel planes or
projection containment. This literature result therefore supplies a known
special family and a possible geometric tool, not a proof of the remaining
curvature branches or of the sharpest-source four-choice algorithm.

Primary source: [Radons, Theorem 1.1 and Section 1.2](https://arxiv.org/html/2105.00555v3).
