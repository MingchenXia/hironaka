# Verification of the 11 October 2026 extensions

These are additive extensions of v0.1 (`919f71bc846dc7904ba91f172d1b1b6a05424596`). The 351 original mathematical modules and all 42 original API theorems are byte-for-byte unchanged. The umbrella adds imports; the README documents the stronger results and remaining limitations.

The four new extension modules contain **40 named mathematical declarations: 38 theorems and two definitions**. Six new support modules restore **29** genuine original declarations omitted by the first extraction. The resulting library has 362 modules including the umbrella. Support restoration is not counted as new mathematical proof production.

| executed check | result | concrete output |
|---|---|---|
| Original v0.1 baseline `lake build` in the fresh standalone checkout | exit 0, 4124 jobs | [baseline-build.txt](baseline-build.txt) |
| Final standalone `lake build` | exit 0, 4134 jobs, no warnings | [build.txt](build.txt) |
| Original-project `#print axioms` on all 40 authored declarations | exit 0; each uses exactly the three standard axioms | archived in the original project's extension audit |
| `lake test` | exit 0; 42 original API prints plus all 4508 non-internal library declarations use only allowed axioms | [all-axioms.txt](all-axioms.txt) |
| `lake env lean scripts/CheckExtensions.lean` | exit 0; all 40 authored names printed; 101 constants in the ten new modules audited, including internal/generated constants; 69 non-internal declarations | [extension-axioms.txt](extension-axioms.txt) |
| Same-environment comparison of originals and renamed copies | exit 0; 69 declarations compared, 68 syntactically equal and one equal up to definitional unfolding; 62/62 theorem proof terms identical; zero problems | [faithfulness.txt](faithfulness.txt), [faithfulness.json](faithfulness.json) |
| Source scan and original-module preservation | ten new modules scanned, zero incomplete-proof/new-axiom/kernel-bypass/heartbeat/internal-path issues; 351 original modules unchanged | [source-scan.json](source-scan.json) |
| Extension blueprint `latexmk -pdf -interaction=nonstopmode -halt-on-error extensions.tex` | exit 0, eight pages, all references/citations resolved | [blueprint-build.txt](blueprint-build.txt) |
| Full `lake env leanchecker --verbose Hironaka` | exit 0; all 362 library modules replayed, zero errors | [kernel-replay.txt](kernel-replay.txt) |

Allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. The one definitional comparison is the restored `AnalyticDimensionBasics.IsPureDim`; both its type and definition value were checked with `Meta.isDefEq`. The comparison uses the original release comparison engine and the canonical namespace/private-name mapping. Its portable generator is kept with the original project's release tools. Source correspondence and mathematical claims were independently reviewed by all three lanes.

The final destination hashes, exact original revisions and source blocks, added support imports, and two mathematical-docstring cleanups are recorded in [provenance.json](provenance.json). No mathematical statement or proof body was adapted beyond canonical name changes.

## Exact remaining boundary

The former missing component identification (README item 5) and the normal-crossings noncontainment issue (item 7) are proved in the new modules. This does not establish every strongest standard form of Hironaka's theorem. In particular, item 6 remains open: the finite-list coefficients are extracted in order from intermediate residual divisors, and a theorem forcing an SNC-supported residual to be the unit ideal plus disconnected-member refinement is still needed. Items 1–4 and 8–9 retain their original limitations.

The earlier failed extraction builds were diagnostic checks of missing old support declarations. They are not treated as success evidence; only the final complete successful build and audits above are accepted.
