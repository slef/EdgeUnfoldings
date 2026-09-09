# A precise example outside the new simple criteria

The new geometric theorems do not yet cover every octahedron. This is now
checked on a small integer example, rather than inferred only from a sample:

    v =(  0,  0,  0)     w =(-18,83,19)
    u0=( -4, 47, 17)     u1=( -5,37,10)
    u2=(-58, 70,-29)     u3=(-12,93,34).

The eight original facets are w u_i u_(i+1) and v u_(i+1) u_i, with cyclic
indices. The exact checker establishes all of the following:

- v has maximum curvature, but its four patches have two inward corners, so
  the zero/one-patch theorem does not apply.
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

A separate targeted search covered all 22 currently open fixed-source failure
classes for 120 seconds each: 7,140 optimizer runs and 3,109,962 objective
evaluations. No positive simultaneous-overlap candidate was found. Many best
scores were close to numerical zero. This excludes **no further class** and
provides no universal certificate. Coordinates, bounds, guards, and outcomes
are retained in `results/octa-targeted-session.json`.

## Where to focus next

The displayed example has three large-curvature vertices forming a face,
with small-curvature opposites. This suggests studying the geometry around
that face and how the three outer patches can be moved. It is a lead from
an example, not a proved characterization of every remaining shape.
The full octahedron theorem, the global four-choice rule, and the general
forms of L and F remain open.
