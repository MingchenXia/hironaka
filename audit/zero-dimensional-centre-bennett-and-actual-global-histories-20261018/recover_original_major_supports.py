"""Recover complete original prerequisites without editing old public mathematics."""
from pathlib import Path
import ast, hashlib, json, re, subprocess, sys

A = Path(__file__).resolve().parent
ROOT = A.parents[1]
SOURCE = Path('/workspace/archon-nakamaye-main')
NATIVE = Path('/workspace/archon-nakamaye/TranscendentalNakamaye')
REV = 'bae7068afc70d624cd8563fd4291436195a7f25f'
sha = lambda b: hashlib.sha256(b).hexdigest()
sys.path.insert(0, str(ROOT / 'scripts'))
import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2', '3', '4']])
flat = names.flattened_short()
fq = re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'
                + '|'.join(flat) + r')\.(?=[\w«])')
frozen = ROOT / 'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
function = next(n for n in ast.parse(frozen.read_text()).body
                if isinstance(n, ast.FunctionDef) and n.name == 'relocate')
exec(compile(ast.Module(body=[function], type_ignores=[]), str(frozen), 'exec'))
records = []

def parent(short):
    module = 'TranscendentalNakamaye.Pending.' + short
    path = 'TranscendentalNakamaye/' + module.replace('.', '/') + '.lean'
    raw = subprocess.check_output(['git', '-C', str(SOURCE), 'show', REV + ':' + path])
    assert raw == (NATIVE / (module.replace('.', '/') + '.lean')).read_bytes()
    ip = NATIVE / '.lake/build/lib/lean' / (module.replace('.', '/') + '.ilean')
    return module, path, raw.decode(), ip, json.loads(ip.read_text())['decls']

def decl(data, suffix):
    module, path, text, ip, decls = data
    choices = [(n, r) for n, r in decls.items() if n.endswith('.' + suffix)]
    assert len(choices) == 1, (module, suffix)
    name, r = choices[0]
    lines = text.splitlines(keepends=True)
    sl, sc, el, ec = r[:4]
    start = len(''.join(lines[:sl])) + sc
    end = len(''.join(lines[:el])) + ec
    block = text[start:end]
    assert text.count(block) == 1
    sidecar = module.split('.')[-1] + '-' + suffix + '-original.lean.txt'
    (A / sidecar).write_text(block)
    return block, {'name': name, 'compiler_source_range': r[:4],
                   'source_byte_range': [len(text[:start].encode()), len(text[:end].encode())],
                   'complete_original_declaration': sidecar,
                   'complete_original_declaration_sha256': sha(block.encode())}

def write(data, short, joined, imports, declarations, classification, omissions=None):
    module, path, text, ip, _ = data
    output = ('/- Complete original prerequisites; statements and mathematical proofs are unchanged. -/\n'
              + ''.join('import ' + m + '\n' for m in imports) + '\n' + relocate(joined))
    destination = 'Hironaka/Support/' + short + '.lean'
    context_path = A / 'original-instance-context-restorations.json'
    original_instances = json.loads(context_path.read_text()).get('Hironaka.Support.' + short, []) if context_path.exists() else []
    for context in original_instances:
        assert output.count(context['before']) == 1
        output = output.replace(context['before'], context['after'], 1)
    p = ROOT / destination
    if p.exists() and p.read_text() != output:
        previous = json.loads((A / 'original-major-support-provenance.json').read_text())
        known = next(r for r in previous if r['destination_path'] == destination)
        assert sha(p.read_bytes()) == known['destination_sha256'], ('Foreign support edit', p)
    p.write_text(output)
    for d in declarations:
        block = (A / d['complete_original_declaration']).read_text()
        assert output.count(relocate(block)) == 1
    records.append({'published_source_revision': REV, 'source_parent_module': module,
                    'source_parent_path': path, 'source_parent_sha256': sha(text.encode()),
                    'compiler_ilean_sha256': sha(ip.read_bytes()),
                    'destination_module': 'Hironaka.Support.' + short,
                    'destination_path': destination, 'destination_sha256': sha(output.encode()),
                    'classification': classification, 'original_context_source': joined,
                    'original_context_sha256': sha(joined.encode()),
                    'pure_existing_or_new_original_support_imports': imports,
                    'complete_original_declarations': declarations,
                    'recorded_context_omissions': omissions or [],
                    'declaration_local_original_instance_contexts': original_instances, 'proof_tokens_edited': 0})

# All original standard-monomial declarations except the one already published.
d = parent('HironakaActualFormalStandardMonomialHS')
b, omitted = decl(d, 'actual_degree_le_of_deglex_lt')
published = ROOT / 'Hironaka/Support/ActualDegreeLexBoundExact.lean'
assert published.read_text().count(relocate(b)) == 1
text = d[2].replace(b, '', 1)
definitions = [decl(d, n.split('.')[-1])[1] for n in d[4]
               if n != omitted['name']]
write(d, 'FormalStandardMonomialHSComplementExact', text,
      ['Hironaka.Support.ActualDegreeLexBoundExact'], definitions,
      'COMPLETE_ORIGINAL_PARENT_REMAINDER_WITH_ALREADY_PUBLISHED_DECLARATION_REUSED',
      [{'reason': 'The complete original degree-bound lemma is already published verbatim.',
        'omitted_original_declaration': omitted, 'published_source': str(published.relative_to(ROOT)),
        'published_source_sha256': sha(published.read_bytes())}])

# This complete source is audited as original support: a lazy foreign namespace
# congruence root may already belong to the preceding public import environment.
d = parent('HironakaActualTranslatedInitialHS')
definitions = [decl(d, n.split('.')[-1])[1] for n in d[4]]
write(d, 'TranslatedInitialHSOriginalExact', d[2], [], definitions,
      'COMPLETE_ORIGINAL_SOURCE_ALL_PUBLIC_ROOTS_COMPARED_TO_ENTIRE_ORIGINAL_PARENT')

d = parent('HolomorphicGermRing')
b, rec = decl(d, 'mk_sub')
bsub, rsub = decl(d, 'eventually_differentiableAt_sub')
text = d[2]
pieces = ['set_option autoImplicit false\n', 'namespace TranscendentalNakamaye.Pending\n', 'open Filter Topology\n',
          'section Differentiability\n',
          'variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]\n',
          bsub, 'end Differentiability\n',
          'variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]\n',
          'namespace HolGerm\n', 'variable {E}\n', b,
          'end HolGerm\n', 'end TranscendentalNakamaye.Pending\n']
assert all(p in text for p in pieces)
write(d, 'HolGermSubExact', '\n\n'.join(pieces),
      ['Hironaka.Analytic.HolomorphicGermRing'], [rsub, rec], 'COMPLETE_ORIGINAL_DECLARATIONS_AND_SECTION_CONTEXT')

d = parent('MarkedIdealTowerTransport')
text = d[2]
header = text[text.index('set_option autoImplicit false'):text.index('/-!')]
context = text[text.index('open Set Filter'):text.index('/-! ### Invariance')]
pieces = [header, context, 'section Transport\n', 'variable {n : ℕ}\n',
          "variable {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)\n",
          'variable {Y Z : CMfd.{u} n}\n']
definitions = []
for suffix in ['length_transport', 'proj_transport']:
    b, rec = decl(d, suffix)
    pieces.append(b)
    definitions.append(rec)
pieces.extend(['end Transport\n', 'end\n', 'end TranscendentalNakamaye.Pending.MarkedIdealTowerTransport\n'])
assert all(p in text for p in pieces)
write(d, 'MarkedTowerTransportEquationsExact', '\n\n'.join(pieces),
      ['Hironaka.MarkedIdeal.MarkedIdealTowerTransport'], definitions,
      'COMPLETE_ORIGINAL_DECLARATIONS_AND_SECTION_CONTEXT')

d = parent('HironakaOriginalGlobalPrincipalization')
text = d[2]
b, rec = decl(d, 'isInvertible_of_open_cover')
prefix = text[text.index('set_option autoImplicit false'):text.index('open FirstPass')]
variables = text[text.index('section OpenDescent'):text.index('/-- A coherent ideal is invertible')]
pieces = [prefix, 'open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences\n',
          'open RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealPullbackCalculus\n',
          variables, b, 'end OpenDescent\n', 'end\n',
          'end TranscendentalNakamaye.Pending.HironakaOriginalGlobalPrincipalization\n']
assert all(p in text for p in pieces)
write(d, 'OriginalInvertibleOpenCoverExact', '\n\n'.join(pieces),
      ['Hironaka.MarkedIdeal.MarkedIdealRestrictOpen', 'Hironaka.MarkedIdeal.HomogenizedIdeal'],
      [rec], 'COMPLETE_ORIGINAL_DECLARATION_AND_RELEVANT_SECTION_CONTEXT',
      [{'reason': 'Original terminal-manifold opens and terminal-only local instances are unused by this general open-cover proof; retained original geometric variables are arbitrary Y.'}])

(A / 'original-major-support-provenance.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps({'original_support_modules': len(records),
                  'complete_original_declarations': sum(len(r['complete_original_declarations']) for r in records),
                  'published_source_revision': REV}))
