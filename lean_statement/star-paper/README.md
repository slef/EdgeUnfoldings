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
- `collect_hovers.py`, `build_hovers.py`: capture real language-server hovers and
  source locations, then bundle portable cards and linked source snapshots.
- `hover-index.json`: token positions, hover/type/documentation data and source
  provenance used by the renderer. `dist/hovers.js` contains the browser data.
- `render.py`: generate the semantic HTML paper.
- `dist/app.js`, `dist/style.css`: authored interaction and presentation.

After a checked Lean checkpoint, update the correspondence manually, then run
`python3 export_sources.py`, `python3 verify_lean.py /path/to/dependencies`,
then `python3 collect_hovers.py /path/to/dependencies`,
`python3 build_hovers.py /path/to/dependencies`, and `python3 render.py`. Update the displayed snapshot date/revision and
verification totals when the checked checkpoint changes. The source manifest
records the revision at export. Re-audit scope labels; they are not inferred
from a theorem name or from successful compilation. Run `python3 validate.py` for static integrity checks before publication.

## Reading interface

Lean inserts expand directly below each paper passage using native HTML
`details`; opening them never scrolls or moves focus to another part of the
page. The inserts and declaration foldouts work without JavaScript. JavaScript adds the annotation visibility toggle and contextual definition cards.
Hover or focus a named identifier in a statement or its surrounding context to
inspect it. Click to pin the card; Enter also moves keyboard focus into it.
Escape and the close button dismiss it without moving the paper. Pointer
hovers wait 450 ms; keyboard focus and clicks remain immediate. A declaration's
own name at its head has no redundant hover card.

When a referenced definition is displayed in the paper, its hover link opens
the appropriate insert and scrolls to that declaration. The full-source link
remains within the insert. Source locations distinguish same-named declarations;
repeated declarations prefer the current insert. Library and other definitions
without an inline counterpart retain their bundled-source links. Direct fragment
links also open any enclosing foldouts.

The official Lean logo (unmodified inline SVG from the navigation at
<https://lean-lang.org/>, retrieved 16 September 2026) means “view the formalization,” not “proved.”
Definitions are labelled “Definition · Formalized”; only theorem declarations
carry “Theorem · Proof checked.” A passage’s scope/coverage is recorded
separately. The proof map provides ordinary navigation links, not annotation
buttons that unexpectedly move the reader.

## Hover provenance

The cards contain Lean 4.29.1 language-server hover responses for the actual
source positions, including instantiated local types and declaration docs.
They distinguish **This project**, **Mathlib**, and **Lean core**. A linked
source definition accompanies each named identifier in the displayed
signatures and contexts. Keywords and punctuation are not identifiers.

For defining occurrences and structure-local binders where Lean returns no
go-to-definition target, the exporter resolves the exact declaration/binding
in the source. Inherited `graph` and `vertices` fields are resolved against
the explicit `EmbeddedCutGraph` parent. Those fallbacks are recorded in the
index; types and documentation still come from Lean. Source excerpts stop at
the declaration boundary; theorem proof bodies are omitted from cards but
remain available in the linked source file.

The capture runs against temporary copies outside a Lake workspace, with
the already built project and dependency paths supplied to Lean. It does
not change or rebuild the proof. Captures are cached in `/tmp/star-hover-cache`;
clear that directory when changing compiled dependencies. The raw capture
is `/tmp/star-hover-raw.json` by default. The static index is committed, so
ordinary page rendering requires no running language server.

All linked library source files are bundled with their original headers and
line numbers. Their hashes, the Lean version and Mathlib revision are in
`hover-index.json`. Re-capture after changing excerpts or their dependencies.
The same project source snapshot and scope caveats as the paper annotations
continue to apply; hovers are inspection aids, not additional proof claims.

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
