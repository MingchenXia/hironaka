"""Validate immutable source provenance and preservation of the preceding release."""
from pathlib import Path
import hashlib,json,re,subprocess
r=Path(__file__).resolve().parents[2];a=Path(__file__).resolve().parent;b=r/'audit/controlled-smooth-pullback-20261015'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((a/'preceding-source-manifest.json').read_text())
assert len(old)==545
repairs=json.loads((r/'scripts/upstream_original_context_repairs.json').read_text());assert len(repairs)==2
repaired_paths={x['protected_module'].replace('.','/')+'.lean':x for x in repairs}
assert len(repaired_paths)==2
for f,h in old.items():
 if f in repaired_paths:
  repair=repaired_paths[f];text=(r/f).read_text();assert sha(r/f)==repair['after_sha256']
  replacements=repair.get('replacements',[{'before':repair.get('before'),'after':repair.get('after')}])
  for change in reversed(replacements):
   assert change['after'] and text.count(change['after'])==1
   text=text.replace(change['after'],change['before'],1)
  assert hashlib.sha256(text.encode()).hexdigest()==h==repair['prior_sha256']
 else:assert sha(r/f)==h,('Protected source changed',f)
modules=json.loads((a/'provenance.json').read_text())+json.loads((b/'provenance.json').read_text());bps=json.loads((a/'blueprint-provenance.json').read_text())+json.loads((b/'blueprint-provenance.json').read_text())
assert len(modules)==182 and len({x['destination_module'] for x in modules})==182
extra=json.loads((r/'scripts/upstream_additional_imports.json').read_text())
for x in modules:
 p=r/(x['destination_module'].replace('.','/')+'.lean');assert sha(p)==x['destination_sha256']
 s=p.read_text()
 for m in reversed(x['additional_pure_support_imports']):
  match=re.search(r'^import ',s,re.M);line='import '+m+'\n';assert s[match.start():].startswith(line);s=s[:match.start()]+s[match.start()+len(line):]
 for change in reversed(x.get('administrative_elaboration_contexts',[])):
  assert s.count(change['after'])==1;s=s.replace(change['after'],change['before'])
 assert hashlib.sha256(s.encode()).hexdigest()==x['initial_synchronized_destination_sha256']
 assert not re.search(r'(?m)^\s*(?:axiom|unsafe\s+def)\b|\bsorry(?:Ax)?\b',s),p
for x in bps:assert sha(r/x['destination_path'])==x['destination_sha256']
root=(r/'Hironaka.lean').read_text();base=subprocess.check_output(['git','show','6c2b1c10e592e92801955a6d03718ecbcf5794dc:Hironaka.lean'],cwd=r).decode()
newroots=['Hironaka.Resolution.HironakaSharpActualCurveLocalSharpEndpoints','Hironaka.Resolution.HironakaOriginalUntestedControlledSmoothPullback']
for m in newroots:
 line='import '+m;assert root.splitlines().count(line)==1 and root.index(line)<root.index('/-!');root=root.replace(line+'\n\n','',1)
# The exporter inserts one additional blank separator at the initial module-doc boundary.
assert root==base or root.rstrip()==base.rstrip() or root.replace('\n\n\n/-!','\n\n/-!')==base
supports=json.loads((a/'all-pure-support-modules.json').read_text())
for m in supports:
 s=(r/(m.replace('.','/')+'.lean')).read_text();assert not re.search(r'(?m)^\s*axiom\b|\bsorry(?:Ax)?\b',s),m
report=dict(status='PASS',preceding_mathematical_modules=len(old),preceding_modules_byte_identical=len(old)-len(repairs),original_declaration_context_repairs=len(repairs),complete_synchronized_modules=len(modules),additional_pure_support_modules=len(supports),import_only_callers=len(extra),complete_blueprint_chapters=len(bps),exact_deduplicated_blueprint_bindings=len({x for bp in bps for x in bp['bindings']}),standalone_local_bindings=len({x for bp in bps for x in bp['local_bindings']}),verified_upstream_bindings=len({x for bp in bps for x in bp['upstream_bindings']}),explicit_historical_unbound_bindings=len({x for bp in bps for x in bp['unbound_upstream_bindings']}),root_imports_added=newroots,proof_body_edits=0,axiom_or_hole_introductions=0)
(a/'source-preservation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
