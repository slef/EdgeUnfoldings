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


## Measurable progress dashboard

`proof_progress.json` holds the named proof obligations and retained quantitative
snapshots. Update a status only when its whole stated domain is proved; link the
argument. Do not count an exact counterexample to a stronger shortcut as closing
the original proof obligation. Append a dated snapshot after each research
session, preserving the old rows. Give unknown denominators explicitly rather
than estimating a global proof percentage. Counts do not estimate difficulty.

`progress_data.py` reads exact region extents and cell/tree counts from the saved
certificate files and their earlier independent replay reports. The five
minus-edge milestones refer to the same chart and center; their comparable
measure is the half-width in every coordinate. The two prism boxes have
*different centers and bounds*; their fractions cannot be added.

The separate prism box B is currently **provisional**. Its fraction is obtained
by summing exact parameter volumes of cells marked successful by the generator;
a complete independent replay has not finished. A slow replay was stopped during
this dashboard update, with no proof conclusion. To obtain that conclusion:

```
python3 -m n6.progress n6/results/prism-balanced-cover.partial.json.gz \
  --output n6/results/prism-balanced-cover.progress.json
```

The checker replays every claimed certified cell, validates the closed binary
subdivision, and leaves all unresolved cells explicit. A false certified label
makes verification fail. Promote the provisional display only after inspecting
a completed report and binding it to the unchanged source file.

Dashboard checks: `node durer_small_n/tests/status_progress.cjs`.
Navigation checks remain in `status_navigation.cjs`. Preserve the original
illustrative prism before its reduction and failure example; its new progress
panel follows the first figure.
