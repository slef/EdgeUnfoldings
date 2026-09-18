# Edge unfolding: interactive Lean proof

Two linked reading pages share exact Lean excerpts, checked proof dependencies,
mathematical typesetting and language-server hover definitions:

- `dist/proof.html`: the full six-vertex proof, adapted from the streamlined
  manuscript, with a case overview and explicit remaining prism obligations.
- `dist/index.html`: the detailed star-unfolding chapter, a private reading
  edition of Kiazyk–Lubiw (2016), Sections 1.1 through the end of Section 2,
  with original Figures 2–5 and a paper-to-Lean correspondence.
The site lives entirely inside the Lean worktree. It does not alter `n6/`,
the main status page, or another worktree. Integration into the public paper
remains a separate change.

## Read and maintain

`dist/proof.html` and `dist/index.html` work as local static pages; all assets and Lean excerpts
are bundled, with no external JavaScript, fonts, or math service required.
Serve `dist/` with any static HTTP server for a preview. The private Sites
identity is recorded in `.openai/hosting.json`.

- `overview.json`: the edited full-proof narrative, case map, mathematical source
  hash and passage-level Lean correspondence; `render_overview.py` renders it.
- `dist/overview.css`: full-proof layout additions to the shared reading design.
- `dist/declaration-links.js`: generated cross-chapter definition destinations.
- `paper.json`: reflowed original text; inline formulas explicitly marked as `\(TeX\)`.
- `math_typesetting.py`, `render_math.cjs`: render all marked formulas at build time
  with pinned KaTeX 0.16.22, producing styled HTML and accessible MathML.
- `vendor/katex/`: the pinned build-time renderer and its MIT license.
- `dist/assets/katex/`: matching local mathematical fonts, stylesheet and license.
- `figures.json`: original captions, using the same explicit math delimiters.
- `annotations.json`: editorial paper coverage, milestone work status and declaration mapping.
- `dist/assets/`: original figure crops and source-page comparisons, extracted
  from the user-supplied journal PDF. The full PDF is not committed.
- `export_sources.py`: export exact declarations, section context, full source,
  and source hashes. Its excerpt extraction follows the current source style;
  inspect regenerated signatures, especially statements containing `let`.
- `CheckExcerpts.lean`: generated checks and axiom queries for all displayed declarations.
- `verify_lean.py`: resolve the declarations against the existing compiled
  project and check every displayed theorem’s axiom report.
- `collect_hovers.py`, `build_hovers.py`: capture real language-server hovers and
  source locations, then bundle portable cards and linked source snapshots.
- `hover-index.json`: token positions, hover/type/documentation data and source
  provenance used by the renderer. `dist/hovers.js` contains the browser data.
- `render.py`: generate the semantic HTML paper.
- `dist/app.js`, `dist/style.css`: authored interaction and presentation.

After a checked Lean checkpoint, update the correspondence manually, then run
`python3 export_sources.py`, `python3 verify_lean.py /path/to/mathlib-project`,
then `python3 collect_hovers.py /path/to/mathlib-project/.lake/packages`,
`python3 build_hovers.py /path/to/mathlib-project/.lake/packages`, and
`python3 render.py`. The exporter records the current date/revision; verification
counts and the displayed audit are derived from that snapshot. The source
manifest records the revision at export. Re-audit scope labels; they are not inferred
from a theorem name or from successful compilation. Run `python3 validate.py` for static integrity checks before publication.

## Mathematical typography

Use `\( ... \)` for every inline formula, including single-letter variables,
in the paper, captions, and editorial explanation text. For example,
`\(S_x\)`, `\(2(n-1)\)`, and `\(\sum_{i=1}^{t}\alpha(e_i)\)`.
Lean excerpts remain exact source code and do not pass through the math renderer.
Run `python3 render.py` and `python3 validate.py` after a typography edit;
there is no need to regenerate the Lean snapshot or hover data.
The renderer rejects invalid TeX. All fonts are bundled, so the mathematical
layout works offline without loading scripts or services in the browser.

## Reading interface

Lean inserts expand directly below each paper passage using native HTML
`details`; opening them never scrolls or moves focus to another part of the
page. The inserts and declaration foldouts work without JavaScript. JavaScript adds the annotation visibility toggle and contextual definition cards.
Hover or focus a named identifier in a statement or its surrounding context to
inspect it. Click to pin the card; Enter also moves keyboard focus into it.
Escape and the close button dismiss it without moving the paper. Pointer
hovers wait 450 ms; keyboard focus and clicks remain immediate. A declaration's
own name at its head has no redundant hover card. This also applies to names
being introduced as structure fields or inductive constructors; references to
those names retain their hover cards.

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

**Paper coverage and work remaining are independent.** The `status` field
describes correspondence with the paper. Each annotation also has a `work`
record: `complete`, `todo` or `beyond`, with a reason, remaining obligations,
additional paper coverage and dependencies on other annotation groups.
The old undifferentiated `gap` field is replaced by `work.remaining` and
`work.beyond`.

Work badges refer specifically to the universal-source milestone documented
in `../STAR_NEXT.md`: the star construction for six-vertex solids with
triangular/quadrilateral faces and a source adjacent to every other vertex.
That milestone is now complete. The actual radial triangles, cofacial leaf
property, global source-angle budget and final assembly are all proved.
`universal_star_embedding` in `UniversalStarEmbedding.lean`
is the main displayed checkpoint, with no assumed separation or angle budget.
Its whole-face consequence covers all solids with at most six vertices and
a universal vertex using the earlier reductions.

Conditional planar components link to the completed constructions supplying
their inputs. Internal original-vertex junctions are excluded by the proved
leaf result; handling them for arbitrary sources is outside this milestone.
Exact boundary-image counts and the standalone exterior-W version of Lemma 3
are extra paper correspondence, not inputs to the direct separation route.
Curve-source unfoldings are deliberately outside the point-star subproject.
An outside-milestone badge never means the corresponding paper claim is proved.

The header derives completion counts from the annotations and audit counts
from the verification record. Updating a proof still requires reviewing the
correspondence and regenerating the snapshot; this page is not a live monitor.

Review these editorial classifications when the target or proof route changes.
Do not infer them from successful compilation, an empty `sorry` search or
the presence of a related declaration. The page shows coverage separately
so that a checked component can remain only a partial match for the paper.

No new mathematical proof or `sorry` was added for these pages. The shared
export now includes the existing main target, explicitly labelled unfinished.
Verification permits `sorryAx` only for that exact target; every other displayed
theorem must use only the three standard allowed axioms. The target is excluded
from the proved-theorem count. The star chapter still displays only proved theorems.

The full-proof annotations independently record whether a result is proved,
partially formalized, not yet proved, or a definition. Their explanation states
whether Lean follows the manuscript’s argument or another route. Each incomplete
passage lists concrete remaining work, including undeclared geometric lemmas. A missing full
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
