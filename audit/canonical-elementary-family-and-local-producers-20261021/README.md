# Canonical families and local analytic producers

This increment exports 373 new physical Lean modules and 349 blueprint chapters
with 1,125 complete written proof environments. It preserves the existing
1,159 Lean sources, 619 blueprint chapters and four frozen verification profiles.

The original source cohorts are pinned to native commits
`4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07` and
`47cef49895832e3bfe492f66e1f2ac68785187dd`.
See [the final publication verification](publication-verification.json) and
[the mathematical scope](../../STATUS.md).

- [Exact source provenance](provenance.json) and [blueprint provenance](blueprint-provenance.json).
- [Independent preservation and source replay](independent-source-replay-review/final-extended-cohort/REPORT.md).
- [All 373 new kernel replays](new-kernel-status.json).
- [Complete expression captures and comparisons](final-per-module-expressions/status.json).
- [Actual typed notation outputs and whole-library dependency scan](all-notation-isolation-final-attempt01/verification.json).
- [Strict mathematical comparison for the ten notation parents](all-notation-classification-final-attempt01/verification.json).
- [Every physical compiled declaration's axiom audit](final-physical-ci-axioms.json).

All mathematical types and whole values/proofs require strict structural
comparison with the frozen comparator. The 60 new compiler-generated notation
definitions retain their raw `BLOCKED_EXACT_DIFFERENCE` reports and receive a
separate source-generation, actual-type and no-logical-dependent classification.
No raw all-root body equality is claimed.

Two complete modules, `HironakaOriginalGlobalOffZero` and
`HironakaOriginalGlobalProperModification`, remain deferred; their complete
sources, chapters and failed comparisons are [retained](deferred-complete-module-partition.json).
General G1, G3, G4, G8 and G9 remain open.

The [blueprint render](blueprint-pdf-final-attempt04/verification.json) uses a
generated typesetting copy. All new chapter reference tokens resolve; the
[render warning review](blueprint-pdf-final-attempt04/typesetting-warning-review-corrected-exact-tokens.json)
discloses 103 unresolved labels referenced only by preserved historical chapters.
Original as-is LaTeX compilation is not claimed.
