from pathlib import Path
import hashlib,importlib.util,json,re,sys
sys.dont_write_bytecode=True
A=Path(__file__).resolve().parent;D=A.parents[1];B=D/'audit/canonical-elementary-family-and-local-producers-20261021';H=lambda b:hashlib.sha256(b).hexdigest()
rows=json.loads((A/'provenance.json').read_text());bps=json.loads((A/'blueprint-provenance.json').read_text());assert len(rows)==len(bps)==9
allmods=['Hironaka',*sorted(str(p.relative_to(D)).removesuffix('.lean').replace('/','.')for p in (D/'Hironaka').rglob('*.lean'))];assert len(allmods)==1542
(A/'all-physical-source-modules.txt').write_text('\n'.join(allmods)+'\n');(A/'new-nine-modules.txt').write_text('\n'.join(r['destination_module']for r in rows)+'\n')
base=B/'additive40-frozen-preparation/physical-ci-axiom-preflight/AllActualStandaloneRootsPhysicalCI.lean';s=base.read_text();s=s.replace('namespace PhysicalCIAxiomAudit','namespace Phase4PhysicalCIAxiomAudit').replace('end PhysicalCIAxiomAudit','end Phase4PhysicalCIAxiomAudit')
s=s.replace('audit/canonical-elementary-family-and-local-producers-20261021/all-standalone-modules.txt','audit/phase4-semantic-producers-20261021/new-nine-modules.txt').replace('audit/canonical-elementary-family-and-local-producers-20261021/final-physical-ci-axioms.json','audit/phase4-semantic-producers-20261021/new-nine-physical-ci-axioms.json')
before='''  unless actual.size == targets.size do
    throwError "Actual standalone module count {actual.size} differs from exact source roster {targets.size}"
  for m in actual do
    unless uniqueTargets.contains m do throwError "Unexpected actual standalone module {m}"'''
after='''  let allPhysical := (← IO.FS.lines "audit/phase4-semantic-producers-20261021/all-physical-source-modules.txt").map String.toName
  unless actual.size == allPhysical.size do
    throwError "Actual imported standalone module count {actual.size} differs from exact physical-source roster {allPhysical.size}"
  for m in actual do
    unless allPhysical.contains m do throwError "Unexpected actual standalone module {m}"
  for target in targets do
    unless actual.contains target do throwError "New physical module not actually imported {target}"
  unless targets.size == 9 do throwError "Expected exactly nine new physical module owners"'''
assert s.count(before)==1;s=s.replace(before,after);s=s.replace('("actual_physical_root_observations", toJson total),','("actual_physical_root_observations", toJson total),\n    ("all_imported_standalone_modules", toJson actual.size),\n    ("old_373_payload_audit_reused_without_replay", toJson true),')
(A/'NewNinePhysicalCIAxioms.lean').write_text(s)
# Literal attachments only from all nine complete exported original chapters.
bindings=sorted({n for r in bps for n in r['local_bindings']});assert len(bindings)==42
(A/'new-nine-literal-bindings.txt').write_text('\n'.join(bindings)+'\n')
check='''import Hironaka
open Lean
run_cmd do
  let env ← getEnv
  let names ← IO.FS.lines "audit/phase4-semantic-producers-20261021/new-nine-literal-bindings.txt"
  unless names.size == 42 do throwError "Changed nine-chapter literal attachment inventory"
  for name in names do
    unless env.contains name.toName do throwError "Missing exact literal local attachment {name}"
  logInfo m!"PASS_EXACT_LITERAL_ATTACHMENTS {names.size}"
''';(A/'CheckNewNineLiteralBindings.lean').write_text(check)
# Capture the entire actual original external node, including its full written proof.
raw=(A/'original-whole-source-captures/hironaka.tex-external-prerequisite.txt').read_text();needle='\\label{hir:base-change-open}';pos=raw.index(needle);start=raw.rfind('\\begin{lemma}',0,pos);proofend=raw.index('\\end{proof}',pos)+len('\\end{proof}');node=raw[start:proofend];assert node.count('\\begin{proof}')==1
(A/'original-whole-source-captures/hir-base-change-open-complete-node.tex.txt').write_text(node)
sp=importlib.util.spec_from_file_location('names',D/'scripts/upstream_namespace_map.py');names=importlib.util.module_from_spec(sp);sp.loader.exec_module(names);names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']])
physical=json.loads((B/'final-physical-ci-axioms.json').read_text());owners={}
for r in physical['all_physical_root_rows']:owners.setdefault(r['actual_name'],[]).append(r['actual_moduleData_owner'])
attachments=[n.strip()for group in re.findall(r'\\lean\{([^}]+)\}',node)for n in group.split(',')];statuses=[{'literal_native_attachment':n,'canonical_public_name':names.rename_const(n),'captured_old_actual_public_owners':owners.get(names.rename_const(n),[]),'local_export_claim_from_pointer':False}for n in attachments]
(A/'external-prerequisite-complete-original-node.json').write_text(json.dumps({'status':'COMPLETE_FIXED_ORIGINAL_EXTERNAL_NODE_PROOF_AND_ATTACHMENTS_CAPTURED','source_revision':'636442a87402a67de1f914cb4120ee28c3ed6ad7','source_path':'TranscendentalNakamaye/blueprint/src/hironaka.tex','source_whole_sha256':H(raw.encode()),'node_source_line':raw[:start].count('\n')+1,'complete_node_sha256':H(node.encode()),'complete_node_capture':'original-whole-source-captures/hir-base-change-open-complete-node.tex.txt','written_proofs':1,'attachments':statuses,'documentation_only':True,'pointer_has_no_leanok_or_empty_proof':True},indent=2)+'\n')
(A/'new-nine-payload-audit-plan.json').write_text(json.dumps({'status':'PREPARED_NINE_NEW_PHYSICAL_CI_PAYLOAD_AXIOM_AND_LITERAL_ATTACHMENT_AUDIT','base_physical_CI_probe':str(base.relative_to(D)),'base_probe_sha256':H(base.read_bytes()),'new_probe_sha256':H((A/'NewNinePhysicalCIAxioms.lean').read_bytes()),'own_type_and_whole_opaque_body_scan_algorithm_unchanged':True,'new_module_owner_roster':9,'all_imported_source_modules':1542,'expected_new_actual_CIs':181,'expected_new_frontend_CIs':15,'literal_local_attachments':42,'old_payload_or_kernel_or_Expr_replay':False},indent=2)+'\n')
print('PREPARED_NEW9_PHYSICAL_PAYLOAD_AXIOMS_AND_42_LITERAL_ATTACHMENTS',len(statuses),'external-node original bindings')
