"""Update current scope only after strict, kernel, compiler and document gates."""
from pathlib import Path
import hashlib,json,subprocess
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
BASE='827676fab01aea03c526b02e5cc13d57568c571d'
AUDIT='audit/noncompact-whole-curve-histories-and-prefix-good-20261018'
OLD='audit/surface-bennett-and-compact-ordered-curves-20261018'
load=lambda name:json.loads((A/name).read_text())
strict=load('strict-all-final-comparison.json');kernel=load('incremental-kernel-replay.json');pdf=load('blueprint-validation.json')
assert strict['status']=='PASS_ALL_ACTUAL_PUBLIC_ROOTS_EXACT_TYPES_WHOLE_VALUES_AND_PROOFS'
assert strict['total_actual_roots']==122 and strict['whole_theorem_proofs']+strict['support_theorem_proofs']==106
assert kernel['status']=='PASS_ALL_NEW_MODULES_AND_CHANGED_KERNEL_ARTIFACTS_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY'
assert kernel['fresh_mathematical_modules']==19 and kernel['total_local_modules']==1160 and kernel['full_sources_and_kernel_parts_unchanged']
assert pdf['pages']==941 and pdf['latex_errors']==0
assert load('all-actual-roots-axiom-and-bindings-receipt.json')['status'].startswith('PASS')
s=subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':README.md'],text=True)
contexts=[]
def replace(before,after,count=1):
 global s
 assert s.count(before)==count,(before,s.count(before));s=s.replace(before,after)
 contexts.append({'before':before,'after':after,'occurrences':count,'kind':'current_scope_update_preserving_historical_mathematical_claims'})
start=s.index("**Bennett's intrinsic Hilbert");end=s.index('**Three of the nine original gaps are closed:',start)
bennett=s[start:s.index('\n\n',start)]
s=s[:start]+f'''**The original smooth-curve sharp history is now constructed without ambient compactness.** The original smooth-curve, ordered SNC, density and regularity hypotheses produce one actual growing blowup sequence with locally finite centre images. Near every compact subset, a finite prefix identifies the same geometric endpoint, strict curve and **every ordered boundary readout**; all later restricted tails are empty. Every prefix is admissible over the original bad locus and an isomorphism over the entire original good locus. The general higher-dimensional G3–G4 statements remain open.

{bennett}

The checked library contains **1,159 mathematical modules**, plus the `Hironaka` import root. All **18,381 actual compiled declarations**, including private and generated declarations, depend only on the three standard axioms. The [current verification receipt]({AUDIT}/final-validation.json) separates the full build, exact original proof comparison and frozen kernel coverage. All 1,140 mathematical sources, complete kernel artifacts and compiler import metadata from the preceding public main remain byte-identical.

'''+s[end:]
replace('| G3 — noncompact global construction | Extend the proved compact smooth-curve finite history and endpoint identification to a complete noncompact global construction and general-dimensional terminal analytic space. |','| G3 — noncompact global construction | Extend the proved noncompact original smooth-curve locally finite history and compact-local endpoint identification to general-dimensional global histories and terminal analytic spaces. |')
replace('| G4 — sharp resolution | Complete noncompact whole-history terminal identification and scheduling; construct the general higher-dimensional defect invariant, decrease and termination. |','| G4 — sharp resolution | Construct the higher-dimensional defect invariant, decrease, termination and sharp global scheduling beyond the completed smooth-curve case. |')
replace('The current proof fronts are general canonical history comparisons, noncompact global blowup histories and scheduling, and higher-dimensional Hilbert–Samuel transformation.','The current proof fronts are general canonical history comparisons, higher-dimensional global histories and sharp scheduling, and higher-dimensional Hilbert–Samuel transformation.')
replace('Noncompact whole-history assembly and general higher-dimensional sharp resolution remain open in this checkpoint.','The later checkpoint below completes the noncompact original smooth-curve whole history; general higher-dimensional sharp resolution remains open.')
replace('The compact original whole-history case is completed below; noncompact whole-history assembly remains open in this checkpoint.','The original smooth-curve whole-history case, including noncompact ambient manifolds, is completed below; the general higher-dimensional driver remains open.',2)
replace('These overlap results feed the later actual global prefix and compact whole-history constructions. Noncompact whole-history assembly remains open in this checkpoint.','These overlap results feed the later actual global prefix and original locally finite whole-history constructions, including noncompact ambient manifolds. The general higher-dimensional driver remains open.')
replace('Noncompact whole-history assembly and the general higher-dimensional sharp driver remain open in this frozen checkpoint.','The noncompact whole-history theorem above retains this compact case; the general higher-dimensional sharp driver remains open.')
marker='## Latest completed subgoals\n\n'
replace(marker,marker+'''* **Noncompact original smooth-curve whole history:** [`exists_original_locallyFinite_sharp_history`](Hironaka/Resolution/HironakaSharpActualCurveLocallyFiniteSharpHistory.lean) constructs the actual growing sequence and the same geometric sharp endpoint from only the original smooth-curve, ordered SNC, density and regularity hypotheses. Centre images are locally finite with closed union. For every compact subset, an actual open neighbourhood and finite prefix identify the projection, conventional strict curve and **all natural-indexed ordered boundary readouts**, with every later restricted tail empty. No compact ambient manifold or preconstructed history certificate is assumed.
* **Every prefix preserves the original good locus:** [`originalGrowingSeq_admissible_sequence`](Hironaka/Resolution/HironakaSharpActualCurveGrowingGoodPreservation.lean) proves admissibility for the whole original ordered ambient boundary over the original sharp bad locus. [`originalGrowingSeq_good_isomorphism`](Hironaka/Resolution/HironakaSharpActualCurveGrowingGoodPreservation.lean) proves that **every actual prefix** is an isomorphism over the entire original good locus. Actual centre support is proved from the same original local recipes.
* **Actual centre-jet and reduced-centre tools:** coherent constant ambient Hilbert–Samuel data give whole finite centre-jet frames, truncation/cocycle dictionaries and a tangent connection. [`hilbertSamuelAt_actual_reduced_centre_strict_le`](Hironaka/Resolution/HironakaActualReducedCentreBennett.lean) derives intrinsic coordinate strict-transform nonincrease from the literal canonical reduced formal centre-power condition, internally producing compatible analytic vertex data. This is a stated additional hypothesis; the general geometric G8 theorem remains open.
''')
start=s.index('The source is the accepted native **429-module**');end=s.index('## Status of the nine original gaps',start)
s=s[:start]+'''The source is the accepted native **443-module** continuation checkpoint, published in [upstream PR169](https://github.com/MingchenXia/archon-nakamaye/pull/169) at [fixed normal Git revision `6a888f9`](https://github.com/MingchenXia/archon-nakamaye/commit/6a888f9dc4155b9ec1407b27223eb37218957159). Relative to the preceding public main, this adds **14 new whole modules**, two complete older original prerequisites and three pure original support modules, with **122 actual compiled roots and 106 entire theorem proofs**. The source/BP provenance covers **16 complete original chapters and two complete original statement/proof extracts**, retaining **48 labelled nodes, 48 original proof environments and 73 local binding spellings**. The one new labelled definition also has a complete proof environment. Later native annihilator, principal-parts and prolongation work is excluded from this fixed checkpoint.

'''+s[end:]
replace('| G3 | A canonical growing sequence and compact-uniform stabilization for initial cosupport of dimension at most one; actual global successor blowups and finite prefixes; a finite original admissible smooth-curve history on compact ambient manifolds, identified with the actual endpoint. | Noncompact whole-history assembly and scheduling, and terminal-space identification in general dimension. |','| G3 | Canonical growing sequences for initial cosupport of dimension at most one; the original smooth-curve locally finite whole history on arbitrary ambient manifolds, with compact-local identification of the same endpoint and every ordered boundary readout. | General-dimensional global histories, scheduling and terminal analytic spaces. |')
replace('| G4 | The compact original smooth-curve finite history, member-product and full ambient TEST conditions, same endpoint, and every ordered boundary readout with exact empty-tail cutoff. | Noncompact whole-history terminal identification and scheduling; the higher-dimensional defect invariant, decrease and termination. |','| G4 | The noncompact original smooth-curve whole history, compact-local terminal squares and empty tails, member-product and full ambient TEST conditions; every prefix is admissible over original bad and isomorphic over original good. | The higher-dimensional defect invariant, decrease, termination and sharp global scheduling. |')
replace('   global sequence existence and its terminal analytic space remain open.','   global sequence existence and its terminal analytic space remain open. The original smooth-curve\n   case now also has a whole locally finite history, with compact-local endpoint identification.')
replace('   original base and stopped-history terminal/open comparison squares. With compact ambient manifold,\n   one finite original admissible history now identifies the same endpoint and all ordered boundary\n   readouts. Noncompact whole-history assembly, scheduling and the higher-dimensional sharp driver remain open.','   original base and stopped-history terminal/open comparison squares. Without ambient compactness,\n   one original locally finite growing history now identifies the same endpoint, strict curve and\n   all ordered boundary readouts near every compact subset, with empty subsequent tails. Every\n   prefix is admissible over original bad and isomorphic over original good. The higher-dimensional\n   sharp driver remains open.')
s=s.replace(OLD+'/CheckAllActualCompiledRoots.lean',AUDIT+'/CheckAllActualCompiledRoots.lean')
start=s.index('## Verification');end=s.index('<details>',start)
s=s[:start]+f'''## Verification

The current [verification report]({AUDIT}/verification.md) and [machine-readable receipt]({AUDIT}/final-validation.json) record separate gates:

* **Build and axioms:** `lake build --wfail` passes all **5,152 jobs**, with zero warnings. All **18,381 actual compiled roots** from all 1,160 local modules, including private/generated and foreign-namespace helpers, use only `propext`, `Classical.choice` and `Quot.sound`. The 73 new, 4,972 synchronized and 6,131 full-document distinct local binding names all resolve.
* **Complete original expressions:** all **122 added actual roots**, including **106 complete theorem proofs**, match their original full types and values. Unchanged ScopedV3 covers every root of all 16 whole modules; unchanged AllV2 covers every actual root of the three supports, compared with rows retained verbatim from their **54 unfiltered original parent roots**. The unchanged structural comparator preserves every Name component, numerical binder/hygiene tag and metadata field. No public root is filtered, no proof is skipped, and no alpha/definitional comparison, erasure or exception is used. The initial single proof-context difference and all unfiltered captures are retained with the exact original-context recovery evidence.
* **Frozen kernel coverage:** **19 mathematical modules and the exact import root** pass fresh installed LeanChecker replay. All **1,140 preceding published mathematical sources, complete kernel parts and compiler import metadata** remain byte-identical to the pinned verified public main. This chain covers all 1,160 local modules; it does not claim a fresh full-library kernel replay.
* **Original source recovery:** 16 whole modules and five complete explicit original support declarations replay from [fixed normal upstream Git](https://github.com/MingchenXia/archon-nakamaye/commit/6a888f9dc4155b9ec1407b27223eb37218957159). One import substitution and one additional pure import expose genuine original prerequisites. One declaration-local existing-instance prefix recovers the original compiled route, before the complete original docstring. All original statements and mathematical proof text remain unchanged; reverse-context byte checks and independent reviews are retained. No old public mathematical source or support is edited.
* **Blueprint and PDF:** 16 added complete original chapters and two complete original statement/proof extracts retain 48 labelled nodes, 48 complete proof environments and 73 local bindings. The synchronized scope has **534 chapter inputs and 1,918 proof environments**; the full book has **619 chapter inputs, 2,389 proof environments and 6,131 local binding names**. The [941-page PDF]({AUDIT}/blueprint-pdf-build/extensions.pdf) renders with no LaTeX errors through the inherited explicitly recorded empty-group disambiguation in an audit-only render copy. All public chapter sources remain unchanged by rendering. The [scope audit]({AUDIT}/docs-inherited-statement-scope-findings.json) retains **36 inherited findings**: 35 historical label placements outside the inspector's supported statement environments and one historical labelled theorem without an attached proof environment in the write-up. These are not claimed repaired. All 48 new labelled statements, including the one definition, have complete proof environments. Existing reference/bookmark warnings and two historical unresolved attachment names remain disclosed.
* **Earlier parser disclosure:** the native280 checkpoint retained three generated notation definitions whose quoted hygiene identifiers differ. Its raw all-1,009-root comparison remains explicitly `BLOCKED_EXACT_DIFFERENCE`; equality of those three bodies remains unclaimed. Their source evidence and axiom/kernel coverage remain in the predecessor chain. All 122 roots added in this checkpoint pass the strict comparison above.

Reproduce source replay and the complete recorded expression comparisons with:

```sh
python3 {AUDIT}/sync_frozen_443.py --source-root /path/to/archon-nakamaye --check
python3 {AUDIT}/recover_original_prerequisites.py --source-root /path/to/archon-nakamaye --check
python3 {AUDIT}/verify_recorded_full_expressions.py
```

The [preceding published verification]({OLD}/verification.md) retains the surface Bennett and compact ordered-curve source, proof and kernel evidence. **G5, G6 and G7 are closed. G1, G2, G3, G4, G8 and G9 remain open in the general forms listed above.**

'''+s[end:]
assert s.count('## Verification')==s.count('## Latest completed subgoals')==1
assert 'Noncompact whole-history assembly'not in s and 'noncompact whole-history assembly'not in s
(ROOT/'README.md').write_text(s);(A/'README-major443-proposed.md').write_text(s)
(A/'docs-readme-current-scope-contexts.json').write_text(json.dumps(contexts,indent=2)+'\n')
print('README443_WRITTEN_WITH_ACTUAL_STRICT_KERNEL_AND_DOCUMENT_GATES',hashlib.sha256(s.encode()).hexdigest())
