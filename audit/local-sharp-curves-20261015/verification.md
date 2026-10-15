# Local sharp curve endpoints and faithful standalone synchronization

The completed new theorem constructs a genuine local sharp endpoint from an original smooth curve, its indexed SNC boundary, density off that boundary, and an arbitrary base point. It produces the open neighbourhood and compactness of its actual cosupport internally, then constructs one finite genuine TEST history. Its endpoint is transverse to the whole accumulated ordered boundary, and the same composite projection is an isomorphism over the whole original local NC good locus.

This is a local curve theorem. It does not construct compatible histories on all overlaps or a general noncompact global sharp resolution. The companion completed subgoal is documented in [the controlled pullback report](../controlled-smooth-pullback-20261015/verification.md).

## Accepted source

The two accepted source checkpoints are `6968ee2596d43d4a5c965a9b0cadad66ec0fc703` (curve endpoint) and `d5d387143239a2776b1e55ef529e65229b120448` (controlled smooth pullback). Both are published in [upstream PR 54](https://github.com/MingchenXia/archon-nakamaye/pull/54), merge `7d0a4d88308ef45c16f25c2e9991e76c1f6ae4b4`. All 182 copied mathematical files, all 182 complete blueprint chapters, and the original parent files used by support fragments have byte provenance to this publicly accessible merge. The replay does not require the private Horizon checkpoint objects.

The standalone addition contains 87 complete modules for the curve closure, 95 complete modules for the controlled pullback closure, and 16 support modules containing complete original declarations omitted by earlier exports. Canonical namespace relocation and explicit import/context changes are recorded in `provenance.json`, the companion audit, and `scripts/upstream_*.json`. No original declaration statement or proof body was rewritten. Two earlier files restore original declaration elaboration contexts; their exact reversible deltas and hashes are recorded in `scripts/upstream_original_context_repairs.json`. The other 543 preceding mathematical modules remain byte identical to standalone base `6c2b1c10e592e92801955a6d03718ecbcf5794dc`.

## Verification gates

Publication waits for all of the following gates. Final results and artifact fingerprints are recorded in `final-validation.json`.

* Full standalone build with `lake build --wfail Hironaka`.
* Exact complete compiled expression comparison for all 2,627 actual constants in the 182 complete modules, including private and generated declarations, definition values and all 2,142 theorem proofs. All expression nodes, binder names and numerical name components are retained. Only explicit namespace/private-owner relocation and witnessed imported binder-owner relocation are applied; there is no alpha-equivalence, definitional-equivalence or numeric-erasure fallback.
* Exact complete expression comparison for all 43 actual support roots, including all 39 theorem proofs, and for the two restored original declarations. Comparators, serializers, owner witnesses and their fingerprints are retained in this audit.
* Axiom checks of all 12,366 actual compiled library roots, including private/generated roots; 2,670 belong to the new modules. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. The ordinary namespace-filtered CI audit is also run, but its smaller count is not used as the complete-root count.
* Independent kernel replay of all 744 local modules, including the import root and every original module. All exported, server and private `.olean` data parts and all mathematical source files are fingerprinted before and after replay. The replay runs after the source/build freeze and without concurrent heavy checks.
* Reversible source guards, independent review, and replay from the public upstream merge using `python3 scripts/verify_from_published_source.py --source-root /path/to/archon-nakamaye`.

The unchanged strict expression comparator is `compare_full_expr_dag.py`. Full large serialized environments live under ignored `.lake/standalone-audit/`; committed comparisons contain their hashes and complete per-module counts. Rejected source-annotation/context attempts and diagnostic comparisons are preserved and are not validation passes. An earlier concurrent kernel run exhausted this workspace's 16 GiB memory limit; its failed log is retained separately from the final isolated replay.

## Blueprint scope

All mathematical statements and proofs in the 182 original chapters are retained, including 770 explicit proof environments. The attachment inventory has 2,235 occurrences and 2,234 distinct names:

* 1,991 names bind to actual declarations compiled in this standalone library (1,381 in new modules and 610 in preceding modules).
* 241 names bind to verified upstream declarations intentionally outside this standalone extraction. Their actual compiled owners, complete source hashes and public source links are recorded in `upstream-only-binding-provenance.json`.
* Two inherited attachment names do not resolve to upstream declarations. They are explicitly marked `upstreamunbound` and their nodes are not presented as fully verified standalone nodes. These are the same two historical unbound names in the native graph baseline.

All 1,375 distinct attachments owned by the 182 new full modules resolve locally. External and unbound attachment metadata affects only the complete inherited blowup-calculus chapter. It does not omit its mathematical prose or relabel upstream-only declarations as locally compiled. Five chapters also apply reversible delimiter/bracing typography repairs, recorded in `scripts/upstream_blueprint_typography.json`.

The full extension blueprint compiles in two LaTeX passes to 485 pages with no LaTeX errors. It retains references to prerequisite chapters outside this standalone blueprint: 618 reference-warning occurrences and 661 LaTeX warnings were already present before the attachment clarification. Six additional hyperref PDF-string warnings concern bookmark text. These warnings are not claimed to have been resolved.

## Remaining mathematical frontier

General higher-dimensional invariants and their actual history descent, general sharp defect termination, noncompact global scheduling/gluing, full Hilbert–Samuel transformation theory, abstract analytic/algebraic categories, and general NC input remain open. The next source-first routes are comparison of the actual local curve histories on overlaps and production of current lower-cosupport membership for actual retained positive member branches. Research drafts alone are not counted as proved Lean modules.
