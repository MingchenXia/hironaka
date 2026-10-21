# Offline additive40 installation preparation

This is an offline source/provenance plan, **not** a standalone mathematical verification receipt. It invokes no Lean, build, kernel replay, or Expr exporter/comparator. It changes no production Lean, blueprint, master, or Git HEAD.

The source is ordinary Git in `/workspace/archon-publish`, fixed at `47cef49895832e3bfe492f66e1f2ac68785187dd`; the immutable earlier source is `4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07`. No private ledger is needed.

## Exact cohort and prepared material

- Final45 minus the existing accepted five gives **40 entire source modules and 40 entire source-facing chapters**. The five are listed in `excluded-five.json`; their source and BP blobs are identical at both fixed revisions and already belong to the historical base325 provenance.
- The selected cohort has **712 distinct actual-root observations, 122 complete proof nodes, 3 ready definition nodes, and 229 literal blueprint bindings**, read from the frozen independent receipts and complete chapters. These are native evidence counts, not new standalone results.
- All 122 original BP proof bodies are retained exactly after the frozen namespace relocation. No source declaration, proof body, root, or chapter is selected out or erased.
- `original/` contains the complete fixed source/BP blobs. `candidate/` contains their proposed standalone paths. Nothing here has been installed.
- `module-provenance-plan.json`, `blueprint-provenance-plan.json`, `module-renames.tsv`, `actual-root-name-relocations.json`, and `literal-blueprint-bindings.json` give exact identities and hashes. `topological-modules.txt` is the 40-module import order.
- The unchanged release contract is captured in `frozen-contracts/`; the existing sync/provenance inputs are captured in `frozen-inputs/`. `input-fingerprints.json` identifies every input. Whole Lean copies use only the established release header and the frozen import/namespace relocation, with **zero new administrative edits or support imports** in this initial candidate.

## Retained323 dependency partition

The historical map has 325 entries. The effective base retains **323** and excludes these two whole modules:

- `Hironaka.Resolution.HironakaOriginalGlobalOffZero`
- `Hironaka.Resolution.HironakaOriginalGlobalProperModification`

Their physical files are treated as unavailable for this check. `base323-availability.json` records both independently reproducible closures:

- Native transitive import closure: 1,364 modules. All 1,324 prior dependencies are byte-identical at the two fixed ordinary commits. There are no additional unlisted post-base modules.
- Effective candidate/standalone import closure: 993 modules, including the actual retained-base administrative/support imports.
- **Neither closure reaches either deferred module.** There are no missing imports. Direct imports outside historical base325 are 29 edges to preserved old public modules, listed in `outside-base325-dependencies.json`; they require no new source copy.

These are static import checks. Full constant-dependency, actual owner, type/value, elaboration, and kernel gates remain pending.

## Exact collision and blueprint flags

There are no destination module/chapter path collisions, no duplicate new root names, and no handwritten source-owner declaration collisions. Four public-name overlaps are **foreign generated helpers** already observed in older compiled metadata:

| New owner | Existing generated root |
|---|---|
| RelativePointChartFactorization | `Hironaka.HironakaActualAnalyticBlowupTaylor.actualAnalyticBlowupPullback.eq_1` |
| RelativePointChartFactorization | `Hironaka.HironakaHolomorphicJetChartInvariance.compAlgHom.congr_simp` |
| RelativePolynomialRehomogenization | `Hironaka.HironakaActualNormalAxisDehomogenization.actualDehomogenizedNormalPolynomialEval.eq_1` |
| NormalCrossingsIntrinsicStratumCentre | `Hironaka.HironakaNormalCrossingsMultiplicityStrata.branchMultiplicity.congr_simp` |

`collision-preflight.json` preserves every observation and existing owner. These overlaps are **not** permission to erase/filter/rename roots or assume whole-expression equality. Actual imported-owner and complete type/value checks must resolve them later.

The complete new chapters have 137 labels with no new/old label collision. Static scanning finds 14 uses of seven old labels lacking a declaration in the existing standalone files. Six of those labels are already referenced by existing chapters; `mc:coefficient-restriction-support` is the seventh. `blueprint-prerequisite-resolution-plan.json` gives the exact fixed source parents/lines and captures all seven complete original nodes with their proofs in `reference-prerequisite-nodes/`. These captures are **reference-only**, not selected extra chapters or installed anchors. Root/frontier must choose the approved BP integration without altering original candidate proofs. All flags remain explicit in `blueprint-static-checks.json`.

## Seven notation-parent source-generation gate

`verify_seven_notation_source_generation.py` follows the existing principal-parts three-parent source-generation verifier. It replays the **entire** fixed ordinary blob through the frozen release recipe and compares the complete candidate bytes. It additionally checks exact local notation clauses and their preceding variable/include context.

The initial candidate gate covers seven parents and 14 literal clauses. The expected 42 generated frontend definitions remain **unconfirmed pending actual original/public typed witnesses**. This source gate makes no parser/Macro/Unexpander classification, parser-body equality, no-dependent, mathematical whole-Expr, kernel, or axiom claim. No roots are excluded.

Current receipt: `seven-notation-source-generation-initial.json`. If actual frontier context commands/imports are later required, retain the initial receipt and supply explicitly recorded per-parent edits via `--contexts`, the actual `--public-root`, and a **new** `--receipt` filename. Every entire public byte and unchanged notation context must replay again. Root owns the separate 10-parent/60-definition actual classifier.

## Installation handoff after retained323 critical gates

1. Check `artifact-manifest.json` and the fixed source/provenance fingerprints. Resolve the four helper-owner and seven BP-reference flags through the approved exact protocols.
2. Install complete chapters before source files. The files `candidate-blueprint-inputs.txt` and `candidate-root-imports.txt` are proposed append blocks only; no existing master/root was edited.
3. Install exactly the 40 candidate source files with overwrite guards. Preserve the retained323, deferred-two decision, old public sources, and existing BP masters.
4. Run the normal author/fresh standalone elaboration, native, all-actual-module-root, kernel, whole type/value Expr, axiom, literal binding, and reproducible source/BP gates. Native receipts alone do not discharge these.
5. If administrative context commands are needed, record them exactly and replay the whole source-generation gate. Do not change mathematical declarations, proofs, notation clauses, or the frozen comparator.

The preparation scripts can regenerate static candidates and checks only. `prepare_offline.py` writes solely within this directory; `check_base323_offline.py` performs the static closure pass. Neither is an installer.
