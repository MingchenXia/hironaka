from pathlib import Path
import hashlib,json,re,subprocess,ast,sys
A=Path(__file__).resolve().parent; P=A.parent; D=P.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
v3=D/'audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean'
assert sha(v3.read_bytes())=='1679359968f3ee3bef887163f5fe8a2f57df6ff293f30ad8e83825fa72cb3755'
source=v3.read_text(); records=json.loads((P/'new-support-provenance.json').read_text())
mods=list(dict.fromkeys((r['source_module'],r['destination_module']) for r in records))
assert len(mods)==3 and len(records)==8
(A/'original-modules.tsv').write_text(''.join(a+'\t'+b+'\n' for a,b in mods))
(A/'public-modules.tsv').write_text(''.join(b+'\t'+b+'\n' for a,b in mods))
oldmap=(D/'audit/phase4-semantic-producers-20261021/exact-module-renames.tsv').read_text()
(A/'exact-module-renames.tsv').write_text(''.join(a+'\t'+b+'\n' for a,b in mods)+oldmap)
# Every serializer definition remains literally the frozen V3 source.
# Only add a selected-original-root variant of the existing export operation.
start=source.index('def exportModuleData ');stop=source.index('\nend HironakaNativeMigrationCanonical',start)
selected=source[start:stop].replace('def exportModuleData (env : Environment)', 'def exportSelectedModuleData (selected : NameSet) (env : Environment)',1)
needle='      for ci in env.header.moduleData[i]!.constants do\n'
assert selected.count(needle)==1
selected=selected.replace(needle,needle+'        unless selected.contains ci.name do continue\n',1)
selected=selected.replace('EXPORTED ALL {count} actual moduleData constants;', 'EXPORTED SELECTED {count} actual original moduleData constants;')
out=source[:stop]+'\n'+selected+source[stop:]
needle='    -- Map only private names occurring in complete expressions of every own\n'
selector='''    -- Scope is determined by ALL actual public moduleData roots, with no filters.
    -- Only their unique original names in the paired actual parent are serialized.
    let mut selected : Lean.NameSet := {}
    let mut selectedWitnesses : Array Lean.Json := #[]
    for (oldMod,newMod) in oldModules do
      let some oi := env.header.moduleNames.findIdx? (· == oldMod)
        | throw (IO.userError s!"Original owner missing {oldMod}")
      let some ni := env.header.moduleNames.findIdx? (· == newMod)
        | throw (IO.userError s!"Public owner missing {newMod}")
      for copy in env.header.moduleData[ni]!.constants do
        let originals := env.header.moduleData[oi]!.constants.filter fun ci =>
          HironakaNativeMigrationCanonical.renamePrivate moduleRenames ci.name == copy.name
        unless originals.size == 1 do
          throw (IO.userError s!"No unique original for actual public root {newMod} {copy.name}: {originals.size}")
        let original := originals[0]!
        unless original.kind == copy.kind do
          throw (IO.userError s!"Constant kind differs {original.name} / {copy.name}")
        selected := selected.insert original.name
        selectedWitnesses := selectedWitnesses.push (Lean.Json.mkObj [
          ("actual_public_module",Lean.toJson newMod.toString),
          ("actual_public_root",Lean.toJson copy.name.toString),
          ("actual_original_module",Lean.toJson oldMod.toString),
          ("actual_original_root",Lean.toJson original.name.toString)])
    IO.FS.writeFile (mapOut ++ ".root-coverage.json") (Lean.Json.arr selectedWitnesses).pretty
'''
assert out.count(needle)==1;out=out.replace(needle,selector+needle,1)
needle='        for ci in env.header.moduleData[i]!.constants do\n          required := required.insert ci.name'
assert out.count(needle)==1;out=out.replace(needle,'        for ci in env.header.moduleData[i]!.constants do\n          unless selected.contains ci.name do continue\n          required := required.insert ci.name',1)
out=out.replace('HironakaNativeMigrationCanonical.exportModuleData env oldModules renames oldOut','HironakaNativeMigrationCanonical.exportSelectedModuleData selected env oldModules renames oldOut',1)
# kind is serialized by the unchanged V3 function; comparing actual kinds here
# is just an earlier coverage assertion, not a change to proof serialization.
out=out.replace('unless original.kind == copy.kind do','unless HironakaNativeMigrationCanonical.kind original == HironakaNativeMigrationCanonical.kind copy do')
(A/'BoundedSelectedSupportV3.lean').write_text(out)
prefix=source[:start]
assert out.startswith(prefix)
# Independently replay the exact raw fragments against published ordinary Git.
sys.path.insert(0,str(D/'scripts'));import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']])
flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
reference=D/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
node=next(n for n in ast.parse(reference.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='relocate')
exec(compile(ast.Module(body=[node],type_ignores=[]),str(reference),'exec'))
for r in records:
 raw=subprocess.check_output(['git','-C','/workspace/archon-publish','show',r['source_revision']+':'+r['source_path']])
 assert sha(raw)==r['source_parent_sha256']
 frag=(P/r['raw_capture']).read_bytes();assert sha(frag)==r['source_complete_declaration_sha256'] and raw.count(frag)==1
 pub=(D/r['destination_path']).read_bytes();assert sha(pub)==r['destination_sha256'] and pub.count(relocate(frag.decode()).encode())==1
(A/'preparation.json').write_text(json.dumps({'status':'PREPARED_BOUNDED_ALL_ACTUAL_NEW_SUPPORT_ROOTS','support_modules':3,'complete_original_declarations':8,'independent_exact_published_source_fragment_replay':'PASS','frozen_v3_sha256':sha(v3.read_bytes()),'unchanged_serializer_prefix_sha256':sha(prefix.encode()),'derived_bounded_exporter_sha256':sha(out.encode()),'serializer_prefix_byte_identical':True,'only_scope_selector_and_selected_export_entry_added':True,'original_whole_parent_replay':False,'public_roots_filtered':False,'proof_or_binder_or_suffix_erasure':False},indent=2)+'\n')
print('PREPARED_BOUNDED_SUPPORT_EXPORT_EXACT_SOURCE_REPLAY_PASS')
