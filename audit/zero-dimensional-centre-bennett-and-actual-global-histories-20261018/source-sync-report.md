# Major395 source and blueprint synchronization

Status: complete source-only recovery with exact normal published Git replay passing. The source is the fixed ordinary published revision `bae7068afc70d624cd8563fd4291436195a7f25f`, project tree `5a85ea9bf4fa0e296e1e19d047a2d98579afaf97`; accepted native checkpoint metadata is `8230607eccbe39a30d5cdbd252781cfbe48d4dc8`. No private ledger is needed.

The main provenance covers 57 complete whole-source modules: all 49 accepted delta modules, four older original formal parents, and the four preserved stalk parents. This step creates 43 Lean files (39 missing delta modules plus four formal parents). The existing repaired derivative module and eight other existing draft modules remain byte-identical. The sole changed existing draft module is PointExceptionalInitialForm, restoring its original HomogeneousInitialHS import now that the complete parent is available. The four previous stalk module files remain byte-identical.

The blueprint provenance covers 59 complete original chapters: all 49 delta chapters and ten older producer chapters discovered uniquely by their own namespace in the pinned v47 inventory's original Lean bindings. They contain 162 complete proof environments, 171 labelled nodes, and 353 distinct local Lean bindings under the unchanged frozen annotation profile. The 49 missing blueprint files were written before the new Lean modules. Existing ten draft chapters remain byte-identical. The master retains all 518 existing inputs and appends 49, reaching 567; the root retains every existing import and adds 43 missing core imports, so all 49 delta modules now have direct imports.

Every source is reconstructed by the existing frozen relocate function and standard header. Changes consist only of the three requested added support imports, four newly requested original-parent import substitutions, and the already verified stalk BiholomorphicWholeStalkHS support substitution. Derivative support import placement is preserved exactly from repair checkpoint `4f034e0dab92eacb4375ab09a38515b63ccbd7cc`. The initial copy guard caught a different import ordering before overwriting the derivative module; the proposed source and failed script log are retained, and the recipe was corrected without changing any proof.

The 1,042 preceding public mathematical source digests pass before and after synchronization. Frozen namespace, annotation, typography and relocation files match the verified repair checkpoint. The source-only script writes no compiled artifact and runs no build, kernel replay, expression export, Git mutation or network action. Existing kernel preservation is owned by the parent lane and is not claimed as freshly checked here.

Reproduce the read-only source gate from the public project root:

```bash
python audit/zero-dimensional-centre-bennett-and-actual-global-histories-20261018/sync_frozen_395.py --source-root /path/to/ordinary/native/git/checkout --check
```

Primary manifests: `provenance.json`, `blueprint-provenance.json`, `older-blueprint-discovery.json`, `source-document-integration.json`, `source-sync-owned-paths.json`, `frozen-source-profile-sha256.json`, `old-public-source-preservation.json`, and `published-source-replay.json`. They record all exact owned paths, source/final hashes, pure import contexts, existing repair prehashes, whole proof-context hashes, root insertions and master insertions.

Claim class: imported boundary, complete original source now present. Consumer: the accepted major395 module cohort and its intrinsic stalk/formal dependencies. Source replay is verified; compilation, ALL expression comparison, support classification, axiom review, kernel preservation and independent root review remain in the parent lane. Honesty reviewer: skipped in this fixed-source recovery worker; parent owns the independent review. No source theorem or general resolution completion is asserted.
