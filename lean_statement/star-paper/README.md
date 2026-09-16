# Star unfolding: annotated paper

A private reading edition of Kiazyk–Lubiw (2016), Sections 1.1 through the end
of Section 2, with original Figures 2–5 and a paper-to-Lean correspondence.
The site lives entirely inside the Lean worktree. It does not alter `n6/`,
the main status page, or another worktree. Integration into the public paper
remains a separate change.

## Read and maintain

`dist/index.html` works as a local static page; all assets and Lean excerpts
are bundled, with no external JavaScript, fonts, or math service required.
Serve `dist/` with any static HTTP server for a preview. The private Sites
identity is recorded in `.openai/hosting.json`.

- `paper.json`: reflowed original text; mathematical notation normalized.
- `figures.json`: original captions.
- `annotations.json`: editorial scope/status judgments and declaration mapping.
- `dist/assets/`: original figure crops and source-page comparisons, extracted
  from the user-supplied journal PDF. The full PDF is not committed.
- `export_sources.py`: export exact declarations, section context, full source,
  and source hashes. Its excerpt extraction follows the current source style;
  inspect regenerated signatures, especially statements containing `let`.
- `CheckExcerpts.lean`: generated checks and axiom queries for all 50 declarations.
- `verify_lean.py`: resolve the declarations against the existing compiled
  project and check all 31 theorem axiom reports.
- `render.py`: generate the semantic HTML paper.
- `dist/app.js`, `dist/style.css`: authored interaction and presentation.

After a checked Lean checkpoint, update the correspondence manually, then run
`python3 export_sources.py`, `python3 verify_lean.py /path/to/dependencies`,
and `python3 render.py`. Update the displayed snapshot date/revision and
verification totals when the checked checkpoint changes. The source manifest
records the revision at export. Re-audit scope labels; they are not inferred
from a theorem name or from successful compilation. Run `python3 validate.py` for static integrity checks before publication.

## Status semantics

No new mathematical proof or `sorry` was added for this page. A missing full
statement is distinct from a declaration containing `sorry`; a checked
conditional planar theorem is distinct from the construction of its inputs.
The full paper Theorem 1 and Lemma 3 remain unfinished in this formalization.
`starCuts` currently means straight cofacial cuts; `CutTreeCharts` requires
original cut vertices to be leaves. These restrictions are visible in the UI.

The excerpt audit is a documentation check, not another proof of geometric
equivalence between the paper and the code. The source-page images allow the
transcription to be checked independently. Two journal wording issues are
retained and explained: “surface area” in the induction paragraph, and the
omitted π/2 offset in “to αᵢ”.

The original text and figures retain their original rights. Keep this reading
edition private unless public reproduction is separately cleared. Hosting
uses a separate source-only publishing mirror; never push the parent project
or create a nested Git repository inside this documentation directory.
