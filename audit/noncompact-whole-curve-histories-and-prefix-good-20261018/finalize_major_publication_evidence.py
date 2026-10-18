"""Aggregate independently reviewed source, strict, kernel and document gates."""
from pathlib import Path
import hashlib,json,re,subprocess
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
load=lambda name:json.loads((A/name).read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
required=['published-source-replay.json','reverse-original-context-source-guard.json','major443-build-receipt.json','all-actual-roots-axiom-and-bindings-receipt.json','strict-all-final-comparison.json','independent-math-review-original-instance-context.json','independent-root-final-source-and-strict-review.json','incremental-kernel-replay.json','accepted-native443-verification.json','docs-completion-receipt.json','independent-root-readme-and-scope-review.json']
for name in required:assert load(name)['status'].startswith('PASS'),name
build=(A/'build-full-major443.log').read_text();assert'Build completed successfully (5152 jobs).'in build and not re.search(r'^.*warning:',build,re.M)
for p in A.glob('incremental-build-*.log'):assert not re.search(r'^.*warning:',p.read_text(),re.M),p.name
strict=load('strict-all-final-comparison.json');assert strict['total_actual_roots']==122 and strict['whole_theorem_proofs']+strict['support_theorem_proofs']==106
assert strict['whole_original_modules']==16 and strict['support_original_modules']==3 and strict['full_unfiltered_native_support_parent_roots']==54 and strict['native_captures_byte_identical_to_first_frozen_attempt']
kernel=load('incremental-kernel-replay.json');assert kernel['fresh_mathematical_modules']==19 and kernel['total_local_modules']==1160 and kernel['full_sources_and_kernel_parts_unchanged']
assert load('kernel-artifacts-before.json')==load('kernel-artifacts-after.json')
for p,h in load('strict-frozen-tool-profiles.json').items():assert sha(ROOT/p)==h,p
for p,h in load('strict-final-gate-hashes.json').items():assert sha(A/p)==h,p
for r in load('strict-capture-source-and-kernel-snapshot.json'):
 for root,key in[(ROOT,'public'),(Path('/workspace/archon-nakamaye/TranscendentalNakamaye'),'native')]:
  stem=r[key+'_module'].replace('.','/');assert sha(root/(stem+'.lean'))==r[key+'_source_sha256'];assert sha(root/'.lake/build/lib/lean'/(stem+'.olean'))==r[key+'_olean_sha256']
for p,h in load('blueprint-all-input-source-digests.json').items():assert sha(ROOT/p)==h,p
for p,h in load('docs-completion-receipt.json')['fixed_binding_inventory_sha256'].items():assert sha(A/p)==h,p
assert'PASS_REPLAY_ALL_122_COMPLETE_RECORDED_TYPES_VALUES_AND_106_PROOFS'in(A/'recorded-expression-replay.log').read_text()
docs=load('blueprint-validation.json');assert docs['pages']==941 and docs['latex_errors']==0 and docs['inherited_full_document_strict_statement_scope_findings']==36
assert docs['provenance_chapters']==18 and docs['provenance_complete_original_proofs']==48 and docs['new_strict_statement_scope_findings']==docs['provenance_labelled_definitions_without_proof']==0
assert sha(A/docs['pdf_path'])==docs['pdf_sha256']
finaldocs=dict(docs);finaldocs.update(status='PASS_NEW_SCOPE_BINDINGS_AND_FULL_PDF_WITH_36_DISCLOSED_INHERITED_SCOPE_FINDINGS',compiled_binding_probe_status='PASS_ALL73_NEW_4972_SYNCHRONIZED_6131_WHOLE_DOCUMENT_BINDINGS',axiom_probe_status='PASS_ALL18381_ACTUAL_LOCAL_ROOTS_STANDARD_THREE_ONLY',pdf_validation_status='PASS941_PAGES_0_LATEX_ERRORS_WITH_INHERITED_RENDER_CONTEXT_AND_WARNINGS',publication_status='ALL_SOURCE_STRICT_KERNEL_DOCS_GATES_PASS; GitHub handled separately',preparation_receipt_preserved_unchanged='blueprint-validation.json')
(A/'blueprint-validation-final.json').write_text(json.dumps(finaldocs,indent=2)+'\n')
readme=(ROOT/'README.md').read_text();assert readme==(A/'README-major443-proposed.md').read_text()
assert all(s in readme for s in['1,159','18,381','122','106','19 mathematical','941-page','G5, G6 and G7 are closed','G1, G2, G3, G4, G8 and G9 remain open'])
assert sha(ROOT/'README.md')in json.dumps(load('independent-root-readme-and-scope-review.json'))
assert subprocess.check_output(['git','-C','/workspace/archon-nakamaye','rev-parse','HEAD'],text=True).strip()=='ffc38f7ddaa48c283969cd34425c75b3becfa6d4'
report='''# Noncompact original smooth-curve whole histories: public443

Only the original smooth-curve, ordered SNC boundary, density and regularity hypotheses produce the actual global growing history and the same sharp geometric endpoint. The centre images are locally finite with closed union. On an actual neighbourhood of every compact subset, one actual finite prefix identifies the projection, conventional strict curve and every natural-indexed ordered boundary readout; every subsequent restricted tail is empty. Every prefix is admissible over original bad and an isomorphism over original good. This completes the stated noncompact smooth-curve case, without completing higher-dimensional G3/G4. G5/G6/G7 are closed; G1/G2/G3/G4/G8/G9 remain open in their general forms.

The previously proved original surface Bennett, arbitrary-dimensional hypersurface-centre equality and zero-dimensional-centre Bennett cases remain. New jet-frame, tangent-connection and canonical reduced-centre results retain their stated constant-HS and reduced formal centre-power hypotheses. Later native annihilator, principal-parts and prolongation work is outside this frozen source.

## Fixed source and recovery

Normal published native Git `6a888f9dc4155b9ec1407b27223eb37218957159` (PR169), project tree `5361620df281449c007c69f5ff5528d066259455`, publishes accepted source `4774cd3a97737754b463603a2188df4cd48efd84` with source/evidence snapshot `f93543fe4bbec8bd5b2c003a9576f689d8e692a1`. Relative to public main `827676fab01aea03c526b02e5cc13d57568c571d`, the extraction adds 14 new whole modules, 2 complete older originals and 3 pure original support modules containing 5 complete explicit original declarations. Reproducible source replay uses ordinary published Git without a private ledger.

One core import substitution and one additional pure support import expose actual original prerequisites. Exactly one declaration-local existing `SubsemiringClass.toAddSubmonoidClass` priority recovers the native elaboration route, before the complete original docstring. Reversing these contexts restores all 16 complete frozen namespace relocations byte for byte; all 3 supports replay exact original context/declaration generators. Types, mathematical proof text and docstrings are unchanged. The initial single mismatch, both complete unfiltered captures and complete 72-step ancestor evidence are retained losslessly. Two earlier missing-original-namespace compiler attempts remain explicit historical evidence; no proof resource option changes or expression waivers were used.

## Separate verification gates

* Configured full build: 5,152 jobs, zero warnings, serial new-module compilation and one Lean thread.
* Actual moduleData axiom audit: 18,381 roots / 1,160 modules, standard three axioms only. All 73 new, 4,972 synchronized and 6,131 entire-document local binding spellings resolve exactly.
* Every 122 actual new root has an exact complete type and whole value, including 106 entire theorem proofs. Unchanged ScopedV3 covers all 115 actual roots of 16 whole modules. Unchanged AllV2 retains all 54 native parent roots and compares every 7 actual public support root to original rows verbatim. No public root selection/filter, skipped proof, extra-name permission, alpha/defeq comparison, erasure or fallback is used. Final native captures equal the first attempt byte for byte. All five final captures are losslessly retained and replay with the unchanged structural comparator.
* Installed LeanChecker freshly replays 19 mathematical modules and the exact import root. All 1,140 prior published sources, complete kernel parts, compiler import metadata and actual direct imports match the pinned verified baseline exactly. All current sources/parts/import metadata remain unchanged through replay. Coverage uses exact prior artifacts; no fresh full-library kernel replay is claimed.
* Earlier native280 three generated parser bodies remain explicitly unclaimed, with prior source/axiom/kernel evidence retained. None of this checkpoint's 122 roots is excepted.

## Original blueprints and PDF

The 16 complete original chapters and 2 complete original statement/proof extracts preserve 48 labelled nodes, 48 complete proof environments and 73 local bindings. All new statements, including the one labelled definition, have a complete proof. The synchronized 534 inputs contain 1,918 proofs and 4,972 local bindings; the full 619-input book contains 2,389 proofs and 6,131 local bindings. Every 601 prior public chapter remains byte-identical; master changes are additive inputs and recorded source/count metadata.

The 941-page PDF renders with zero LaTeX errors and stable references. The inherited audit-only empty-group context changes no public source. There are 703 inherited reference-warning occurrences and no introduced reference/citation spelling. All 36 inherited statement-inspector findings remain unchanged: 35 historical label placements and one historical labelled theorem without an attached write-up proof. They are not claimed repaired; all 48 new statements pass. The two historical unresolved attachment names remain disclosed.

The final machine receipt, source/proof/context reviews, kernel coverage, README and reproduction scripts provide exact evidence. Remote publication and branch cleanup are recorded separately after verified push, PR and merge.
'''
(A/'verification.md').write_text(report)
files=required+['strict-final-gate-hashes.json','retained-final-expression-captures.json','recorded-expression-replay.log','blueprint-validation-final.json','previous-frozen-kernel-data-reuse.json','old-public-kernel-initial-guard.json','verification.md']
result={'status':'PASS_FROZEN_MAJOR_NONCOMPACT_ORIGINAL_CURVE_WHOLE_HISTORY_AND_PREFIX_GOOD_PUBLIC443','normal_published_native_revision':'6a888f9dc4155b9ec1407b27223eb37218957159','accepted_native_source_checkpoint':'4774cd3a97737754b463603a2188df4cd48efd84','native_project_tree':'5361620df281449c007c69f5ff5528d066259455','previous_public_main':'827676fab01aea03c526b02e5cc13d57568c571d','full_hironaka_complete':False,'closed_general_gaps':['G5','G6','G7'],'open_general_gaps':['G1','G2','G3','G4','G8','G9'],'mathematical_modules':1159,'all_actual_compiled_roots':18381,'added_mathematical_modules':19,'added_actual_roots':122,'added_complete_theorem_proofs':106,'whole_original_modules':16,'new_support_modules':3,'configured_full_build_jobs':5152,'build_warnings':0,'fresh_kernel_math_modules':19,'fresh_kernel_import_root':True,'reused_published_math_modules_with_exact_sources_and_complete_kernel_parts':1140,'all_current_sources_and_kernel_parts_frozen_during_replay':True,'new_blueprint_inputs':18,'new_whole_original_blueprint_chapters':16,'new_complete_original_statement_proof_extracts':2,'new_blueprint_labels':48,'new_blueprint_proof_environments':48,'synchronized_inputs':534,'synchronized_proof_environments':1918,'synchronized_local_bindings':4972,'whole_document_inputs':619,'whole_document_proof_environments':2389,'whole_document_local_bindings':6131,'inherited_whole_document_scope_findings':36,'inherited_findings_claimed_repaired':False,'pdf_pages':941,'pdf_sha256':docs['pdf_sha256'],'readme_sha256':sha(ROOT/'README.md'),'new_root_filters_or_waivers_or_erasures':0,'frozen_tools_modified':False,'source_mathematical_type_or_proof_tokens_edited':0,'evidence_sha256':{name:sha(A/name)for name in files},'github_publication':'PENDING_PUSH_PR_MERGE; all gates passed; standing explicit user authorization'}
(A/'final-validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='evidence_sha256'}))
