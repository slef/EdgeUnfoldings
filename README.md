# Edge unfoldings of small convex polytopes (Dürer's problem, n ≤ 6)

Working repository for a human-readable proof that every convex polytope with at most six vertices has a
non-overlapping edge unfolding, in the style of J. DiBiase's 1990 thesis.

* **Status page** (case tree, figures, interactive octahedron): deployed from `durer_small_n/notes/status.html`
  to GitHub Pages on every push to the default branch, `master`.
* **Current research:** [Lemma L is proved](n6/LEMMA_L_PROOF.md). The selected-slit
  Lemma F problem now reduces to [two finite cut segments](n6/LEMMA_F_CUT_RAYS.md),
  with additional direction subcases proved. The full octahedron and n=6 remain open.
* `HANDOFF.md` — current audit followed by the historical proof account.
* `n6/README.md` — archive integration, exact partial certificates, and reproduction.
* `n6/REVIEW.md` — proof gaps and corrected numerical checks; the full n=6 case remains open in this investigation.
* `durer_small_n/notes/lemmaF.tex` — working notes on Lemma F (the octahedron's far pairs).
* `durer_small_n/notes/dibiase_summary.md` — what DiBiase's thesis does and does not contain.
* `durer_small_n/octa.py` — the geometry module; the other scripts are experiments (see `durer_small_n/README.md`
  and the code map in `HANDOFF.md`).

To rebuild the status page from the saved figures and current notes, run
`python3 durer_small_n/build_status.py` from the repository root.
To check the deployment package, run `python3 durer_small_n/build_pages.py /tmp/edge-unfoldings-site`
and `node durer_small_n/tests/status_deployment.cjs /tmp/edge-unfoldings-site`.
Regenerating scientific figures additionally needs the scientific virtual environment.
