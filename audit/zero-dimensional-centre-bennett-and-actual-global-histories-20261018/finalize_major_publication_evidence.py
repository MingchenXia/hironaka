"""Finalize accurate README and aggregate only already completed independent gates."""
from pathlib import Path
import hashlib,json,re,subprocess
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda n:json.loads((A/n).read_text())
required=['published-source-replay.json','all-original-support-source-replay.json','reverse-original-context-source-guard.json','major395-build-receipt.json','all-actual-roots-axiom-and-bindings-receipt.json','strict-all-final-comparison.json','independent-math-review-public-major-source-context.json','independent-root-final-source-and-strict-review.json','incremental-kernel-replay.json','accepted-native395-verification.json']
for name in required:assert load(name)['status'].startswith('PASS'),(name,load(name)['status'])
assert load('major395-build-receipt.json')['exit_code']==0
build=(A/'build-full-major395.log').read_text();assert 'Build completed successfully (5099 jobs).' in build and not re.search(r'^.*warning:',build,re.M)
strict=load('strict-all-final-comparison.json');assert strict['total_actual_roots']==667 and strict['whole_theorem_proofs']+strict['support_theorem_proofs']==547
kernel=load('incremental-kernel-replay.json');assert kernel['fresh_mathematical_modules']==54 and kernel['previous_verified_repair_modules_exact_source_and_kernel_parts_reused']==10 and kernel['total_local_modules']==1107
assert kernel['full_sources_and_kernel_parts_unchanged']
assert load('kernel-artifacts-before.json')==load('kernel-artifacts-after.json')
for name,digest in load('strict-frozen-tool-profiles.json').items():assert sha(ROOT/name)==digest
for item in load('strict-capture-source-and-kernel-snapshot.json'):
 assert sha(ROOT/(item['public_module'].replace('.','/')+'.lean'))==item['public_source_sha256']
 assert sha(ROOT/'.lake/build/lib/lean'/(item['public_module'].replace('.','/')+'.olean'))==item['public_olean_sha256']
for path,digest in load('blueprint-all-input-source-digests.json').items():assert sha(ROOT/path)==digest,path
for name,digest in load('docs-completion-receipt.json')['fixed_binding_inventory_sha256'].items():assert sha(A/name)==digest,name
assert 'PASS_REPLAY_ALL_667_COMPLETE_RECORDED_TYPES_VALUES_AND_547_PROOFS' in (A/'recorded-expression-replay.log').read_text()
docs=load('blueprint-validation.json');assert docs['pages']==880 and docs['latex_errors']==0 and docs['inherited_full_document_strict_statement_scope_findings']==36 and docs['new_strict_statement_scope_findings']==0
assert docs['provenance_chapters']==59 and docs['provenance_complete_original_proofs']==162 and docs['provenance_labelled_definitions_without_proof']==9
assert sha(A/docs['pdf_path'])==docs['pdf_sha256']
finaldocs=dict(docs);finaldocs.update({'status':'PASS_NEW_SCOPE_BINDINGS_AND_FULL_PDF_WITH_36_DISCLOSED_INHERITED_SCOPE_FINDINGS','compiled_binding_probe_status':'PASS_ALL353_NEW_4731_SYNCHRONIZED_5890_WHOLE_DOCUMENT_LOCAL_BINDINGS','axiom_probe_status':'PASS_ALL17944_ACTUAL_LOCAL_COMPILED_ROOTS_STANDARD_THREE_ONLY','pdf_validation_status':'PASS880_PAGES_0_LATEX_ERRORS_WITH_RECORDED_RENDER_CONTEXT_AND_INHERITED_WARNINGS','publication_status':'ALL_SOURCE_STRICT_KERNEL_DOCS_GATES_PASS; GitHub publication handled separately','compiled_binding_and_axiom_receipt':'all-actual-roots-axiom-and-bindings-receipt.json','normal_native395_compiled_binding_receipt':'accepted-native395-verification.json','preparation_receipt_preserved_unchanged':'blueprint-validation.json'})
(A/'blueprint-validation-final.json').write_text(json.dumps(finaldocs,indent=2)+'\n')
README=(A/'README-major395-proposed.md').read_text()
assert all(s in README for s in ['1,106','17,944','667','547','54 mathematical','880-page','G5, G6 and G7 are closed','G1, G2, G3, G4, G8 and G9 remain open'])
(ROOT/'README.md').write_text(README)
report='''# Actual zero-dimensional-centre Bennett: frozen public395

The original intrinsic Hilbert–Samuel function of a genuine geometric strict transform is no greater than the original value, at every point and every natural order, for blowups along actual zero-dimensional smooth centres. The theorem uses original `IsBlowupAlong`, actual `RegularAtDim … 0` centre regularity and analyticity of the subset. The above-centre companion applies to every subset without analyticity or coherence. No HS comparison certificate is assumed.

General positive-dimensional-centre Bennett remains open. G5/G6/G7 are closed; general G1/G2/G3/G4/G8/G9 remain open. The smooth-curve additions supply genuine global successor blowups/centres and original-base finite prefixes, including empty-centre stages, plus stopped-history terminal/open comparison squares. Complete global terminal identification, compact-uniform scheduling and the higher-dimensional sharp driver remain open.

## Frozen source and support honesty

Normal upstream Git `bae7068afc70d624cd8563fd4291436195a7f25f` (PR150), project tree `5a85ea9bf4fa0e296e1e19d047a2d98579afaf97`, publishes accepted mathematical source checkpoint `8230607eccbe39a30d5cdbd252781cfbe48d4dc8`. All reproduction uses normal Git; the private ledger is not needed. Later native work is excluded.

The increment beyond public main `7f043d57b4052e6f8fc69c4abe4d762114a7666f` adds 57 whole original modules and seven support modules, recovering 49 complete explicit support declarations. Three pure support imports, five parent-import substitutions and one restored original import recover genuine original prerequisites. Six declaration-local existing-instance route prefixes and the exact original unused transport variable command restore the native elaboration context. Reversing these administrative contexts recovers the entire frozen source before recovery byte for byte. Every original statement and mathematical proof token is retained.

Independent math review read all 842 support-source lines and checked all 49 complete original declarations, entire 57 whole-source reconstructions and all 1042 protected old sources. Root additionally checked all 256 source/olean snapshot hashes and the complete strict gate metadata. Retained failed attempts are explicit; they are superseded by the final exact comparison, without tool changes or exceptions.

## Checks

* Configured full `lake build --wfail`:5099 jobs, zero warnings. New 64 module targets compile serially with one Lean thread.
* Every actual local moduleData root:17944 roots/1107 modules, standard three axioms only. All 353 new,4731 synchronized and 5890 full-document local binding names resolve.
* Unchanged ScopedV3 whole exports:571 actual roots/57 modules, all472 theorem proofs exact. Unchanged AllV2 support exports:all96 actual public roots/seven modules, all75 theorem proofs exact. Complete306 native parent roots remain retained; native selection is verbatim for every public root. All667 complete types and values and 547 theorem proofs match structurally, preserving names, all numerical suffixes, binders and metadata, with zero skips, filters, waivers, alpha/defeq shortcuts or erasure.
* Installed LeanChecker freshly replays 54 mathematical modules and the exact import root. Ten added modules retain exact sources and complete kernel parts from verified repair checkpoint `4f034e0dab92eacb4375ab09a38515b63ccbd7cc`. All 1042 preceding published sources and complete kernel parts match the pinned prior verified main. Every source, kernel part and import metadata hash remains unchanged during replay. This covers 1107 modules through exact checkpoint reuse; it does not claim a fresh full-library replay.
* Lossless deterministic gzip captures reproduce all 667 comparisons and 547 complete theorem proofs using the unchanged comparator. Earlier native280 three generated parser bodies remain explicitly unclaimed, as disclosed in the predecessor; none of this increment's roots is excepted.

## Blueprint and PDF scope

The recovered 59 chapters retain 171 labels/162 complete original proof environments/353 local bindings. The synchronized 482 chapters contain 1774 proof environments and4731 local names. The whole 567-chapter document has 2245 proof environments and 5890 local names. Definitions genuinely needing no separate proof are counted as definitions; no proof is manufactured.

The 880-page PDF (SHA `f87aabb4395c1481614db4749a80853fa92c2e7765e05af3b243e9890c0aaa6f`) renders with zero LaTeX errors and stable cross-references. One audit-only `\\\\[H]`→`\\\\{}[H]` empty-group disambiguation preserves public chapter bytes and mathematical content; its original failed TeX run and source are retained.703 reference warnings,72 missing destinations and six bookmark warnings remain disclosed, with no introduced reference/citation spelling. The scope inspector retains 36 inherited findings (35 historical label placements outside supported statement environments and one old labelled theorem lacking an attached proof environment in the write-up); these are not claimed repaired. All 59 new source chapters and the 395 native continuation scope pass their respective strict statement/proof audits.

See `final-validation.json`, `blueprint-validation-final.json`, all independent reviews, and `README.md` for exact evidence paths and reproduction commands. GitHub publication and branch cleanup are recorded separately after the push/PR/merge succeeds.
'''
(A/'verification.md').write_text(report)
files=required+['strict-final-gate-hashes.json','all-original-support-source-replay.json','retained-final-expression-captures.json','recorded-expression-replay.log','blueprint-validation-final.json','docs-completion-receipt.json','readme-mathematical-scope-review.json','previous-frozen-kernel-data-reuse.json','verification.md']
receipt={'status':'PASS_FROZEN_MAJOR_ACTUAL_ZERO_DIMENSIONAL_CENTRE_BENNETT_PUBLIC395','normal_published_native_revision':'bae7068afc70d624cd8563fd4291436195a7f25f','accepted_native_source_checkpoint':'8230607eccbe39a30d5cdbd252781cfbe48d4dc8','native_project_tree':'5a85ea9bf4fa0e296e1e19d047a2d98579afaf97','previous_public_main':'7f043d57b4052e6f8fc69c4abe4d762114a7666f','frozen_public_mathematical_source_checkpoint':'8add74af09472a5a2b5b1dd8e15bee918db4044f','major_case':'actual zero-dimensional smooth-centre intrinsic geometric Bennett at every point and order','case_hypotheses':'original IsBlowupAlong + actual RegularAtDim0 centre regularity; W analytic globally, arbitrary subset above centre','supplied_HS_output_certificate':False,'full_hironaka_complete':False,'closed_general_gaps':['G5','G6','G7'],'open_general_gaps':['G1','G2','G3','G4','G8','G9'],'mathematical_modules':1106,'all_actual_compiled_roots':17944,'added_mathematical_modules':64,'added_actual_roots':667,'added_complete_theorem_proofs':547,'whole_original_modules':57,'support_modules':7,'complete_explicit_original_support_declarations':49,'configured_full_build_jobs':5099,'build_warnings':0,'fresh_kernel_math_modules':54,'fresh_kernel_import_root':True,'reused_published_math_modules_with_exact_sources_and_complete_kernel_parts':1042,'reused_repair_math_modules_with_exact_sources_and_complete_kernel_parts':10,'all_current_sources_and_compiled_kernel_parts_frozen_during_replay':True,'new_blueprint_chapters':59,'new_blueprint_labels':171,'new_blueprint_proof_environments':162,'synchronized_chapters':482,'synchronized_proof_environments':1774,'synchronized_local_bindings':4731,'whole_document_chapters':567,'whole_document_proof_environments':2245,'whole_document_local_bindings':5890,'inherited_whole_document_scope_findings':36,'inherited_findings_claimed_repaired':False,'pdf_pages':880,'pdf_sha256':docs['pdf_sha256'],'readme_sha256':sha(ROOT/'README.md'),'new_root_filters_or_waivers_or_erasures':0,'frozen_tools_modified':False,'source_mathematical_type_or_proof_tokens_edited':0,'evidence_sha256':{name:sha(A/name) for name in files},'github_publication':'PENDING_PUSH_PR_MERGE; all verification gates passed; user remote authorization persists'}
(A/'final-validation.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k!='evidence_sha256'}))
