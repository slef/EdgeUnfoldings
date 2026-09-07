# Edge unfoldings of small convex polytopes — experiment scripts

* `unfold.py`   — simplicial polytopes: all dual spanning trees, planar development, overlap test
                  (separating-axis test with tolerance; touching allowed; pairs of faces sharing a
                  net vertex are skipped since they lie in disjoint wedges).
* `unfold2.py`  — same for polytopes with non-triangular faces (coplanar hull facets merged).
* `gen.py`      — random polytopes incl. very flat / needle-like ones (log-uniform anisotropic scaling).
* `sample.py n N seed`   — min number of nets over N random n-vertex polytopes.
* `classify.py n seed N` — cut-tree classes up to the type's automorphisms; which classes always contain a net.
* `finer.py`, `rules.py`, `pattern6.py`, `adv6.py` — tests of "star(v) + one pendant edge" (Lemma B).
* `conjC.py n seed N`    — Conjecture C: every vertex star extends to a net.
* `nonsimp6.py`          — the two non-simplicial 6-vertex types without a degree-5 vertex.
* `types6.py`            — enumerates the 7 combinatorial types of 6-vertex polytopes (networkx).
* `geodesic.py`          — shortest surface path between two vertices (small polytopes).
