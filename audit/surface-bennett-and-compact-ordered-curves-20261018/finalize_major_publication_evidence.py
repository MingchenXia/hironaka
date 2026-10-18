"""Aggregate completed source, strict, kernel, review and documentation gates."""
from pathlib import Path
import hashlib,json,re
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
load=lambda name:json.loads((A/name).read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
required=['published-source-replay.json','reverse-original-context-source-guard.json','major429-build-receipt.json','all-actual-roots-axiom-and-bindings-receipt.json','strict-all-final-comparison.json','independent-math-review-original-instance-context.json','independent-root-final-source-and-strict-review.json','incremental-kernel-replay.json','accepted-native429-verification.json','docs-completion-receipt.json','independent-root-readme-and-scope-review.json']
for name in required:assert load(name)['status'].startswith('PASS'),(name,load(name)['status'])
build=(A/'build-full-major429.log').read_text();assert'Build completed successfully (5133 jobs).'in build and not re.search(r'^.*warning:',build,re.M)
for path in A.glob('incremental-build-*.log'):assert not re.search(r'^.*warning:',path.read_text(),re.M),path.name
strict=load('strict-all-final-comparison.json');assert strict['total_actual_roots']==315 and strict['whole_theorem_proofs']==279 and strict['native_capture_byte_identical_to_first_frozen_attempt']
kernel=load('incremental-kernel-replay.json');assert kernel['fresh_mathematical_modules']==34 and kernel['total_local_modules']==1141 and kernel['full_sources_and_kernel_parts_unchanged']
assert load('kernel-artifacts-before.json')==load('kernel-artifacts-after.json')
for name,h in load('strict-frozen-tool-profiles.json').items():assert sha(ROOT/name)==h,name
for name,h in load('strict-final-gate-hashes.json').items():assert sha(A/name)==h,name
for r in load('strict-capture-source-and-kernel-snapshot.json'):
 assert sha(ROOT/(r['public_module'].replace('.','/')+'.lean'))==r['public_source_sha256']
 assert sha(ROOT/'.lake/build/lib/lean'/(r['public_module'].replace('.','/')+'.olean'))==r['public_olean_sha256']
for name,h in load('blueprint-all-input-source-digests.json').items():assert sha(ROOT/name)==h,name
for name,h in load('docs-completion-receipt.json')['fixed_binding_inventory_sha256'].items():assert sha(A/name)==h,name
assert'PASS_REPLAY_ALL_315_COMPLETE_RECORDED_TYPES_VALUES_AND_279_PROOFS'in(A/'recorded-expression-replay.log').read_text()
docs=load('blueprint-validation.json');assert docs['pages']==920 and docs['latex_errors']==0 and docs['inherited_full_document_strict_statement_scope_findings']==36 and docs['new_strict_statement_scope_findings']==0
assert docs['provenance_chapters']==34 and docs['provenance_complete_original_proofs']==96 and docs['provenance_labelled_definitions_without_proof']==0
assert sha(A/docs['pdf_path'])==docs['pdf_sha256']
finaldocs=dict(docs);finaldocs.update(status='PASS_NEW_SCOPE_BINDINGS_AND_FULL_PDF_WITH_36_DISCLOSED_INHERITED_SCOPE_FINDINGS',compiled_binding_probe_status='PASS_ALL168_NEW_4899_SYNCHRONIZED_6058_WHOLE_DOCUMENT_LOCAL_BINDINGS',axiom_probe_status='PASS_ALL18259_ACTUAL_LOCAL_COMPILED_ROOTS_STANDARD_THREE_ONLY',pdf_validation_status='PASS920_PAGES_0_LATEX_ERRORS_WITH_INHERITED_RENDER_CONTEXT_AND_WARNINGS',publication_status='ALL_SOURCE_STRICT_KERNEL_DOCS_GATES_PASS; GitHub publication handled separately',preparation_receipt_preserved_unchanged='blueprint-validation.json')
(A/'blueprint-validation-final.json').write_text(json.dumps(finaldocs,indent=2)+'\n')
readme=(ROOT/'README.md').read_text();assert readme==(A/'README-major429-proposed.md').read_text()
assert all(x in readme for x in ['1,140','18,259','315','279','34 mathematical','920-page','G5, G6 and G7 are closed','G1, G2, G3, G4, G8 and G9 remain open'])
review=load('independent-root-readme-and-scope-review.json')
assert sha(ROOT/'README.md') in json.dumps(review), 'Independent README review must pin its actual hash'
report='''# Intrinsic surface Bennett and compact ordered curve histories: public429

The original full blowup predicate and analyticity of the subset imply intrinsic Hilbert–Samuel nonincrease for actual complex surface blowups, at every point and every natural order. No Hilbert–Samuel output certificate is assumed. Hypersurface-centre points in any ambient dimension give equality for arbitrary subsets. The previous zero-dimensional smooth-centre case is retained. The general positive-dimensional-centre case in ambient dimension at least three and normal codimension at least two remains open.

Original smooth-curve geometry, ordered SNC boundary, density and ordinary ambient compactness produce one actual finite admissible global history, identified with the same geometric endpoint and all ordered boundary readouts, including original positions, empty entries, defaulted indices and the exact cutoff. Noncompact whole-history additions after the freeze are excluded. G5/G6/G7 are closed; general G1/G2/G3/G4/G8/G9 remain open.

## Fixed source and faithful context recovery

Normal upstream Git `07d2a1e3242cc2c37bab1d8eab4847246555c8eb` (PR162), project tree `5aaaf165ba219c10029133c7fa0ad1e7104d5d92`, publishes accepted checkpoint `a7b004cbf5a9a8f05459635e90bae0835c967c27`. Source replay requires ordinary published Git, with no private ledger. The increment beyond public main `964b18f9c1cf70c263f4d4351b826413450ddf74` adds 34 complete original modules and 34 complete original blueprints. Two pure import substitutions reuse already verified original support without editing it.

Two declaration-local existing `SubsemiringClass.toAddSubmonoidClass` instance prefixes recover the original proof elaboration route. They precede the entire original docstrings. Reversing the two prefixes recovers the complete first-attempt sources byte for byte; reversing all four recorded administrative contexts recovers every complete frozen original namespace relocation. Every original type and mathematical proof token is retained. Independent whole-source/context reviews and the final strict gate review are retained. Both initial expression discrepancies, the initial parser-rejected prefix placement, full source snapshots and lossless unfiltered captures remain explicit historical evidence. No waiver or canonical-tool edit was used.

## Verification

* The configured full `lake build --wfail` passes 5,133 jobs with zero warnings. New targets compile serially with one Lean thread; no proof resource options change.
* Every actual local moduleData root passes the standard-three-axiom allowlist: 18,259 roots / 1,141 modules. All 168 new, 4,899 synchronized and 6,058 full-document exact local binding names resolve.
* Unchanged ScopedV3 exports compare every 315 actual new root and all 279 complete theorem proofs structurally, including full types, whole values, private/generated/foreign names, numerical components, binders and metadata. Complete root sets agree; no skips, filters, waivers, alpha/defeq comparison or erasure. The final native capture is byte-identical to the first frozen attempt. Lossless deterministic gzip captures reproduce the same 315 comparisons and 279 proofs using the unchanged comparator.
* Installed LeanChecker freshly replays 34 mathematical modules and the exact import root. All 1,106 preceding mathematical sources, complete kernel parts and actual compiler import metadata match the pinned verified public main exactly. Every current source, kernel part and import metadata hash remains unchanged through replay. This covers 1,141 modules through exact prior-artifact reuse; no fresh full-library replay is claimed.
* Earlier native280 three generated parser bodies remain explicitly unclaimed, with their predecessor source/axiom/kernel evidence retained. None of this increment's 315 roots is excepted.

## Blueprint and PDF

The new 34 chapters preserve 96 labelled nodes, 96 complete proof environments and 168 local bindings. All seven new labelled definitions have complete proof environments. The synchronized 516 chapters contain 1,870 proof environments and 4,899 local names. The full 601-chapter document contains 2,341 proof environments and 6,058 local names; all labels are unique.

The 920-page PDF renders with zero LaTeX errors and stable cross-references. The inherited audit-only empty-group disambiguation preserves every public chapter byte; its exact render context remains recorded. There are 703 inherited reference-warning occurrences and no introduced reference or citation spelling. The 36 inherited statement-scope findings are unchanged: 35 historical label placements outside supported statement environments and one historical labelled theorem without an attached proof environment in the write-up. None is claimed repaired; the new 34 chapters have no such findings. Two historical unresolved attachment names remain explicit.

`final-validation.json`, `blueprint-validation-final.json`, the independent reviews and README give the exact evidence and reproduction commands. GitHub publication and branch cleanup are recorded separately after verified push, PR and merge.
'''
(A/'verification.md').write_text(report)
files=required+['strict-final-gate-hashes.json','retained-final-expression-captures.json','recorded-expression-replay.log','blueprint-validation-final.json','previous-frozen-kernel-data-reuse.json','old-public-kernel-initial-guard.json','verification.md']
result={'status':'PASS_FROZEN_MAJOR_INTRINSIC_SURFACE_BENNETT_AND_COMPACT_ORDERED_CURVES_PUBLIC429','normal_published_native_revision':'07d2a1e3242cc2c37bab1d8eab4847246555c8eb','accepted_native_source_checkpoint':'a7b004cbf5a9a8f05459635e90bae0835c967c27','native_project_tree':'5aaaf165ba219c10029133c7fa0ad1e7104d5d92','previous_public_main':'964b18f9c1cf70c263f4d4351b826413450ddf74','major_cases':['Original full actual surface blowup intrinsic Bennett, all points and all orders, analytic subset','Any-dimensional hypersurface-centre intrinsic HS equality, arbitrary subset','Actual compact original smooth-curve admissible history, same endpoint and every ordered boundary readout'],'full_hironaka_complete':False,'closed_general_gaps':['G5','G6','G7'],'open_general_gaps':['G1','G2','G3','G4','G8','G9'],'mathematical_modules':1140,'all_actual_compiled_roots':18259,'added_mathematical_modules':34,'added_actual_roots':315,'added_complete_theorem_proofs':279,'whole_original_modules':34,'new_support_modules':0,'configured_full_build_jobs':5133,'build_warnings':0,'fresh_kernel_math_modules':34,'fresh_kernel_import_root':True,'reused_published_math_modules_with_exact_sources_and_complete_kernel_parts':1106,'all_current_sources_and_kernel_parts_frozen_during_replay':True,'new_blueprint_chapters':34,'new_blueprint_labels':96,'new_blueprint_proof_environments':96,'synchronized_chapters':516,'synchronized_proof_environments':1870,'synchronized_local_bindings':4899,'whole_document_chapters':601,'whole_document_proof_environments':2341,'whole_document_local_bindings':6058,'inherited_whole_document_scope_findings':36,'inherited_findings_claimed_repaired':False,'pdf_pages':920,'pdf_sha256':docs['pdf_sha256'],'readme_sha256':sha(ROOT/'README.md'),'new_root_filters_or_waivers_or_erasures':0,'frozen_tools_modified':False,'source_mathematical_type_or_proof_tokens_edited':0,'evidence_sha256':{name:sha(A/name)for name in files},'github_publication':'PENDING_PUSH_PR_MERGE; all verification gates passed; standing explicit user authorization'}
(A/'final-validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='evidence_sha256'}))
