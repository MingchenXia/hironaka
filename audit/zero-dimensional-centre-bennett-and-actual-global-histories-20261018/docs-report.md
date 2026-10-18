# Blueprint documentation and PDF preparation

The fixed native395 source-scope audit passes for all 395 original chapters: 1,205 labelled nodes, 1,190 nonempty complete proof environments, 44 labelled definitions, and 15 definitions without a separate proof. Every labelled non-definition has a complete following proof. This is a source-text statement/proof-scope result, not a compiled Lean result.

| Public source scope | Chapters | Source labels | Proof environments | Local binding spellings |
| --- | ---: | ---: | ---: | ---: |
| Current provenance | 59 | 171 | 162 | 353 |
| Synchronized union | 482 | 1,814 | 1,774 | 4,731 |
| Full document | 567 | 2,341 | 2,245 | 5,890 |

The 59-chapter provenance includes ten previously synchronized chapters; the newly added 49 inputs contribute 135 proof environments and 307 new local binding spellings. The native395 count describes the frozen native continuation and is not increased by adding public copies of older prerequisite chapters. All 59 recovered chapters pass the strict labelled-statement inspector, as do all 395 native chapters. All full-document proof environments are balanced and nonempty; source labels are unique.

The strict inspector reports 36 unchanged historical findings across the full document: 35 label-coverage limitations and one missing following proof for the labelled non-definition `hir:submersion-relative-coordinate-ideal` in unchanged `blueprint/hironaka-smooth-submersion-relative-restriction-extension.tex`. Five findings lie within the synchronized union. No historical proof was manufactured or silently excluded; complete details are in `docs-inherited-statement-scope-findings.json`. The master metadata prose and date were updated under exact `docs-master-documentation-contexts.json` records to state this scope honestly. No chapter source was edited. The main sync replay logic and its expected-master integration metadata were adjusted to replay those explicit documentation contexts; the parent must refresh its normal Git source replay receipt.

The prepared PDF is `blueprint-pdf-build/extensions.pdf`: **880 pages**, **4,383,336 bytes**, SHA-256 `f87aabb4395c1481614db4749a80853fa92c2e7765e05af3b243e9890c0aaa6f`. Three final TeX passes completed, with no LaTeX errors and stable cross-reference metadata. The first render attempt failed at original HomogeneousInitialHS line 28, where `\\[H]` after a cases row break is parsed as an invalid optional spacing argument. Its raw stdout, TeX log and exact original source are retained. The retry uses the explicitly recorded `\\{}[H]` markup fix in an audit-owned render-source copy only. Public source and frozen typography-map bytes are unchanged. `docs-render-source-provenance.json` records every render input and that one context.

Final TeX warnings: 703 references, 72 missing PDF destinations, 6 bookmark warnings, 1 amsmath warning, 0 citation warnings, 6 overfull boxes and 53 underfull boxes. Reference and missing-destination inventories exactly match the predecessor; no new unresolved reference or citation spelling was introduced. Raw logs and `docs-tex-warning-inventory.json` retain the details. No source proof was rewritten to suppress inherited warnings.

Binding inventories are fixed at 4731 synchronized names and 5890 full-document names. Their SHA-256 values remain exactly those sent before the parent Lean binding check; `new-local-bindings.json` remains 353 names and byte-identical. These lists come from actual source `lean` metadata; this worker does not claim the names compile. Parent compilation, strict expressions, axioms, kernel preservation and independent review remain separate. `blueprint-validation.json` and `docs-completion-receipt.json` deliberately say PREPARED with publication gates pending.

No Lean/AST/kernel operation, Git command, network action, mathematical source edit, global namespace/typography-map edit, or README update occurred in this docs phase. Claim class: source-audited imported blueprint boundary plus prepared PDF artifact. Honesty review: parent owns the independent review; no general mathematical completion is claimed here.
