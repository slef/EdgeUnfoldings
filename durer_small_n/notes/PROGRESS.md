# Maintaining the overview's progress history

The user asked to keep successive research notes with their results.

Add each new research snapshot to `progress_history.json`, with its date,
a short title, HTML body, and the relevant result IDs in `results`. Preserve
older snapshots as historical records; explain later corrections in a new
entry. Put the newest snapshot first. The overview displays the whole history
in a collapsed block at the top and filters it beside the associated results.

Keep the current header and result explanations current. Distinguish a general
proof, a certificate covering a bounded family, an exact counterexample to a
specific intermediate claim, numerical evidence, and an unresolved search.
Primary explanatory links should go to actual result sections on the page;
raw source files belong under optional technical details.

Build `status.html` from `status_template.html` with `build_status.py`. The
user-facing page is `status.html`; the template has unresolved build tokens.
Navigation regression: `node durer_small_n/tests/status_navigation.cjs` from
the repository root. Keep the original illustrative prism ahead of its
reduction and failure example, and preserve the existing interactive models.
