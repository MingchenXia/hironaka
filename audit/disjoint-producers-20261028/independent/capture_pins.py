from pathlib import Path
import json,hashlib,sys
A=Path(__file__).resolve().parent.parent;D=A.parents[1];plan=json.loads((A/'plan.json').read_text());paths={A/'plan.json',D/'Hironaka.lean',D/'blueprint/extensions.tex'}
paths.update((D/'.lake/build/lib/lean').glob('Hironaka.*'))
for row in plan['source_modules']+plan.get('support_extracts',[]):
 paths.add(D/row['destination_path'])
 if row.get('raw_capture'):paths.add(A/row['raw_capture'])
 if row.get('draft_capture'):paths.add(A/row['draft_capture'])
 if row.get('source_parent_capture'):paths.add(A/row['source_parent_capture'])
 m=row['destination_module'];rel=Path(*m.split('.'))
 for sub in ['lib/lean','ir']:
  base=D/'.lake/build'/sub/rel
  paths.update(base.parent.glob(base.name+'.*'))
for row in plan['blueprints']+plan['documentation_pointers']:
 paths.add(D/row['destination_path'])
 if row.get('raw_capture'):paths.add(A/row['raw_capture'])
for directory in ['external-native-parents','external-native-nodes','full-expressions-owner-correction-attempt02']:
 paths.update(x for x in (A/directory).rglob('*') if x.is_file())
for x in ['actual-inherited-owner-witness.json','external-prerequisite-plan.json','external-prerequisite-index.tex','support-extraction-plan.json','support-original-callees.tex','support-vanishing-zero-locus.tex','source-check-receipt.json']:
 if (A/x).exists():paths.add(A/x)
for row in plan['frozen_tools'].values():paths.add(A/row['capture'])
rows={str(p.relative_to(D)): {'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in sorted(paths) if p.is_file()}
for row in plan['source_modules']+plan.get('support_extracts',[]):
 target=D/'.lake/build/lib/lean'/Path(*row['destination_module'].split('.'))
 assert target.with_suffix('.olean').exists(),str(target)
 assert any(str(k).startswith(str(target.relative_to(D))+'.olean') for k in rows)
out=A/'independent'/sys.argv[1];assert not out.exists();out.write_text(json.dumps(rows,indent=2)+'\n');print(len(rows))
