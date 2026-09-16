# Lean worktree and integration

The Lean formalization belongs in this repository under `lean_statement/`.
Its development branch is `codex/lean-formalization`. On the current machine,
the working checkout is the sibling directory `EdgeUnfoldings-lean-formalization`.
Continue Lean edits there, not in the main `EdgeUnfoldings` checkout.

## Scope and checkpoints

Keep formalization changes, build configuration, and Lean documentation in
`lean_statement/`. The `n6/` manuscript, `n7/` work, and `topological_n5_n6/`
work have separate development histories. Changes to shared paper pages,
navigation, and publication configuration should be coordinated explicitly.

The initial import preserves the existing 892 Lean sources and their
configuration and notes. It starts from repository revision
`5b21be4896f9e178626f1ca4fdcdc7e7458b93dc`.
The complete six-vertex theorem and the broader star theorem remain unfinished;
see [STAR_NEXT.md](STAR_NEXT.md) for the current geometric scope and next gap.
The original `sorry` remains isolated in `Statement.lean`.

Commit meaningful checked checkpoints. Include Lean sources, the toolchain
file, Lake configuration and lockfile, the build helper, and documentation.
Keep `.lake/`, compiled outputs, temporary experiments, and external reference
PDFs out of these commits. The existing `.gitignore` excludes build caches.

## Verification

The project pins Lean in `lean-toolchain` and Mathlib in `lakefile.toml` and
`lake-manifest.json`. From `lean_statement/`, the portable build is:

```sh
lake exe cache get
lake build
lake env lean Statement.lean
```

`lake build` checks the proved library and its axiom audit. The separate
statement check also checks the unfinished target and reports its known hole.

When matching compiled Mathlib dependencies already exist in another local
checkout, the build helper uses those dependencies read-only:

```sh
python3 check.py --dependencies /path/to/matching/mathlib/project --incremental
```

The helper verifies the Mathlib revision and writes all project outputs into
this worktree's own `.lake/build/`. Its default targets include the proved
library, the unfinished statement, and `Audit.lean`. The audit permits only
`propext`, `Classical.choice`, and `Quot.sound` in proved-library dependencies.

## Future interactive paper

Keep the explanatory paper and formalization in the same repository so a
published revision can identify exactly which code was checked. Plan two
complementary documentation layers: a short mathematical guide and a generated
reference for individual Lean declarations.

For each paper claim, record its Lean declaration name, exact hypotheses,
verification status, and a short explanation of the proof. Link to declarations
by stable names, with the published commit identified. A proved special case
must remain visibly distinguished from an unfinished general statement.

Integrate checked Lean checkpoints on their own merits; they need not wait for
the full theorem. Add the paper's navigation and theorem links in a separate,
coordinated change once its intended text and formal correspondence are agreed.
No paper pages or publishing configuration are changed by this initial import.
