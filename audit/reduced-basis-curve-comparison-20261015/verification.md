# Reduced formal standard bases and actual curve-stage comparison

The four synchronized subgoals are canonical reduced formal standard bases, original controlled restriction to a smaller strict carrier, actual curve-defect open restriction, and naturality of the actual first centres and their next blowups. Their complete dependency closure contains 49 whole modules and 49 complete blueprint chapters with 209 original proofs. Three pure support modules recover five complete original declarations. General higher-dimensional Hironaka goals, full presentation construction, overlap gluing and Bennett inequalities remain open.

The source checkpoint is `7726587fed8e52e34c41d069ddd5ed7eee83e33a`. Read-only source reproduction uses normal public upstream merge `d7bd3eabbaa5853f5062bd38e5f358c2d462c1a4`, so the private Horizon ledger is not required. All 743 preceding mathematical source modules are byte-identical; the import root only gains the four recorded imports. The frozen earlier exporter, namespace map and old expression comparators are unchanged.

Validation:

- `build-08-original-import-order.log`: `lake build --wfail`, 4,766 jobs, zero warnings. Earlier unsuccessful support/context attempts are retained as diagnostics.
- `all-actual-roots-final-08.log`: all 796 local modules and 14,022 actual compiled declarations, including private and generated declarations; standard three axioms only. The 52 new modules have 1,656 actual roots; all 810 new blueprint bindings resolve locally.
- `whole-module-full-expression-comparison-final-08.json`: all 1,651 actual roots of all 49 whole modules match complete original types and values, including all 1,381 theorem proofs.
- `fragment-full-expression-comparison.json`: all five actual support roots match their complete original types and proof bodies. No new root is filtered out; original parent declarations outside the five extracted fragments are identified separately.
- `incremental-kernel-replay.json`: all 52 added modules and the changed import-only root pass fresh standard kernel replay, with all source and kernel-data fingerprints identical before and after; 323.39 seconds with one Lean thread. `previous-frozen-kernel-data-reuse.json` verifies that the 743 preceding non-root sources and kernel-data parts are byte-identical to the earlier isolated full 744-module replay. This covers all 796 current local modules and does not claim a fresh full-library replay.
- `published-source-replay.json`: all whole modules, original support declarations and complete blueprint chapters reproduce exactly from public Git after only the recorded namespace relocation, header, pure imports and original declaration-scoped elaboration contexts.
- `blueprint-validation.json`: 231 complete synchronized chapters, 979 complete original proofs, 2,801 distinct local declaration bindings, 241 verified upstream-only bindings and two explicitly unresolved historical attachment names. The full 558-page blueprint compiles with no LaTeX errors. Its 661 LaTeX warnings include 660 prerequisite-reference warnings; six PDF bookmark warnings are also retained. These document warnings are not counted as proof verification failures or silently reported as zero.

The complete expression serializer retains every Name component, universe level, binder annotation, metadata and complete expression constructor. It uses structural equality, not alpha-equivalence or definitional-equivalence. Actual private helpers and generated declarations are included, preserving all numerical indices and suffixes. There is no unfolding, hashing shortcut, fallback or numerical erasure.

Two genuine original subring/reducedness instance paths differ under the standalone import context. `original-subring-context-restorations.json` records 35 declaration-scoped original-instance restorations; no mathematical statement or proof text changes. The original `HolGerm.isReduced` theorem and instance are recovered in a pure support module, using the original pointwise nilpotent proof rather than replacing it with a domain argument. Original import order is retained so unrelated elaboration remains exact.

Five actual new declarations inherit a binder context from the actual legacy callee in `Hironaka.Coherence.CoherentIdealFiniteSpan`; another new declaration inherits the same original callee from `Hironaka.Support.FiniteSpanRangeExact`. The previously frozen nine-rule serializer profile could not distinguish those import owners. `CanonicalStandaloneAllScopedOwnersV3.lean` adds only five exact actual-root entries to select the correctly witnessed owner. Both actual callee owners are proved by `ImportedBinderOwnerNativeProbe.lean` / `ImportedBinderOwnerPublicProbe.lean`, whose logs retain the identical original scope `1599403507` and hygiene seed `44`. All other roots retain the frozen nine rules; all expression, numeric and metadata fields remain complete. The entire profile and serializer delta received independent review in `scoped-owner-peer-review.md`.

The raw complete expression snapshots each exceed GitHub's per-file size limit. `full-expression-artifacts.json` records the complete uncompressed fingerprints and lossless gzip fingerprints; every compression was verified by an exact round trip. The source of the unchanged strict comparator is retained in the preceding audit. Reproduce the complete captured-data comparison with:

```sh
python3 audit/reduced-basis-curve-comparison-20261015/verify_recorded_full_expressions.py
```

The wrapper checks every compressed and uncompressed fingerprint, uses the unchanged complete structural comparator and requires exactly 1,651 whole-module plus five support roots, with no missing or extra names. Its independent review is in `recorded-expression-wrapper-peer-review.md`. This captured-data comparison complements the separate current build, axiom audit and frozen kernel replay.

Reproduce source integrity from a normal upstream checkout with:

```sh
python3 audit/reduced-basis-curve-comparison-20261015/verify_incremental_source.py --source-root /path/to/archon-nakamaye
```

Complete mathematics and support extraction were independently reviewed. Private source PDFs and their page transcriptions are not exported. This checkpoint extends the proved cases and does not close G1, G2, G3, G4, G8 or G9; the original G5, G6 and G7 remain closed.

One trailing space in the whole original `HironakaRelativeNormalGraphWeightAnalyticReconstruction` proof is preserved exactly; `inherited-source-whitespace.json` records the original published line. Authored documentation and tools pass the whitespace check.
