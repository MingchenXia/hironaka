"""Reproduce fixed338 README after each independent source/Expr/kernel/PDF gate."""
from pathlib import Path
import json,re,subprocess
A=Path(__file__).resolve().parent;ROOT=A.parents[1];BASE='2342eead0cdd7bba08acb2456e275a916bab94cf'
REV='f873b1d904f8e63cd9f73e0b5bf6eefb0332093a'
load=lambda n:json.loads((A/n).read_text())
for name,status in [('whole-module-full-expression-comparison.json','EXACT_ALL_FULL_EXPR_DAG_MATCH'),('fragment-full-expression-comparison.json','EXACT_ALL_FULL_EXPR_DAG_MATCH'),('incremental-kernel-replay.json','PASS_ALL_NEW_MODULES_AND_CHANGED_KERNEL_ARTIFACTS_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY'),('blueprint-validation.json','PASS_COMPLETE_BLUEPRINT_LATEX_NO_ERRORS')]:assert load(name)['status']==status
assert 'PASS_ALL_95_RECORDED_ACTUAL_ROOTS_AND_77_COMPLETE_THEOREM_PROOFS_FULL_STRUCTURAL_COMPARISON' in (A/'recorded-full-expression-replay.log').read_text()
s=subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':README.md'],text=True)
link='audit/'+A.name
start=s.index('The checked library contains **1,026 mathematical modules**');stop=s.index('**Three of the nine original gaps are closed:',start)
s=s[:start]+f'''The checked library contains **1,034 mathematical modules**, plus the `Hironaka` import root. All **17,169 actual compiled declarations**, including private and generated declarations, depend only on the three standard axioms. The [verification receipt]({link}/final-validation.json) records fresh frozen kernel replay of all eight added modules and the import root. All 1,026 preceding mathematical sources and their complete kernel-data artifacts remain byte-identical to the verified preceding checkpoint.

The latest completed subgoals compare prepared original values at all source bounds and relative dimensions, construct genuine uniform curve prefixes and their whole open restrictions, and produce nearby analytic generators from original local coherence and the stated coefficient-order input. These results advance G2, G4 and G8; their explicit hypotheses and the remaining general goals are stated below.

'''+s[stop:]
start=s.index('## Latest completed subgoals');stop=s.index('## Status of the nine original gaps',start)
s=s[:start]+f'''## Latest completed subgoals

* **Prepared comparisons at all source bounds and relative dimensions:** [the joint source-bound theorem](Hironaka/Resolution/HironakaOriginalPreparedJointSourceBoundValues.lean) proves the prepared original FULL and StepOne value comparisons for all stated source bounds and every relative dimension, including open and nested-open restrictions. The hypotheses retain the genuine **old canonical prefix and one actual admissible whole cut**, together with the stated original DOMAIN preparation and the same given Cartesian source history. The proof supplies the recursive lower and OWN-large comparisons internally. This closes the prepared all-bound/all-relative-dimension case; an arbitrary noncanonical old prefix, canonicity of the appended history, and the complete terminating driver are separate open goals.
* **Uniform actual curve prefixes and whole open restrictions:** [uniform prefixes](Hironaka/Resolution/HironakaSharpActualCurveUniformPrefixes.lean) retain the exact requested number of stages using empty identity padding, prove independence from additional empty tails, and construct unique stagewise comparisons with cocycles from genuine padded-history comparisons. [Prefix restriction](Hironaka/Resolution/HironakaSharpActualCurveUniformPrefixRestriction.lean) constructs the isomorphism to the entire inverse-image open, proves the full projection square and restricts the old stagewise comparison through the actual flattenings. The previously proved coupled global sharp endpoint, conventional smooth strict curve and reduced Cartier birth boundary remain included. A single global intermediate blowup schedule and the higher-dimensional sharp driver remain open.
* **Actual analytic coefficient data and nearby generators:** [the coefficient-data construction](Hironaka/Resolution/HironakaActualAnalyticVertexCoefficientData.lean) internally produces genuine analytic monic generators of the whole original origin ideal, a common holomorphic coefficient domain and actual coherent principal coefficient ideals. From the stated original coefficient cosupport orders on the coordinate plane it derives the literal reduced-formal-vertex centre-power compatibility, and supplies analytic normalized-member generators whose whole Taylor image is the formal strict ideal. [The nearby theorem](Hironaka/Resolution/HironakaActualAnalyticNearbyVertexGenerators.lean) uses original coherence on a real open neighborhood of zero to make the same origin generating family generate every original stalk on one smaller open. General permissible-centre compatibility, geometric strict-transform identification, transformed stability and Bennett inequalities remain open.

This public snapshot reproduces the accepted native **338-module** continuation checkpoint, published in [upstream PR127](https://github.com/MingchenXia/archon-nakamaye/pull/127) at the [fixed source revision](https://github.com/MingchenXia/archon-nakamaye/commit/{REV}). The increment beyond native333 contains five whole original modules and five complete blueprint chapters: 13 labelled nodes, 12 complete proofs and one genuine mathematical definition without a proof. Three further pure support modules recover three complete original prerequisites with their original contexts. All **95 actual added declarations**, including **77 complete theorem proofs** and all private/generated helpers, match their original complete types and values. Later native work is excluded from these totals.

'''+s[stop:]
rows={
'G2':'| G2 | Original given-history and prepared FULL/StepOne comparisons at all stated source bounds and all relative dimensions, with actual recomputed lower and OWN-large values and open restrictions. | The prepared comparison assumes an old canonical prefix and one actual admissible whole cut. The complete canonical elementary endpoint, general history construction and terminating global scheduling remain open. |',
'G4':'| G4 | Coupled global sharp endpoint data for original smooth curves, conventional strict curve, reduced Cartier birth boundary and genuine finite local presentations; exact-length uniform prefixes, unique stagewise comparisons and whole inverse-image-open restrictions. | A single actual global intermediate blowup history and schedule; the complete higher-dimensional defect invariant, decrease and termination. |',
'G8':'| G8 | Genuine analytic completion and whole Taylor intersections/colons/saturation; actual analytic coefficient data and monic generators; centre compatibility from the stated coefficient cosupport orders, analytic normalized-member generators with whole formal strict ideal image, and nearby original stalk generation from local coherence. | Derive the inputs for general permissible centres, identify the complete geometric strict-transform bridge and transformed presentations, prove stability and Bennett inequalities. |'}
start=s.index('## Status of the nine original gaps')
for gap,row in rows.items():
 a=s.index('| '+gap+' |',start);b=s.index('\n',a);s=s[:a]+row+s[b:]
s=s.replace('audit/analytic-strict-generators-and-coupled-global-endpoint-20261018/CheckAllActualCompiledRoots.lean',link+'/CheckAllActualCompiledRoots.lean')
start=s.index('The current [verification report]',s.index('## Verification'));stop=s.index('<details>',start)
s=s[:start]+f'''The current [verification report]({link}/verification.md) and [machine-readable receipt]({link}/final-validation.json) cover this increment:

* **Build and axioms:** `lake --wfail build` passed all 5,026 jobs with zero warnings. All 17,169 actual library roots use only `propext`, `Classical.choice` and `Quot.sound`. All 5,494 distinct local declaration bindings in the full blueprint resolve in the compiled library.
* **Complete expression comparison:** all **95 added actual roots** match their original full types and values, including all **77 complete theorem proofs**, private/generated helpers, projections, constructors and recursors. The unchanged ScopedOwnersV3 and AllV2 serializers and structural comparator retain full Name components, binder names and metadata, with no alpha/definitional comparison or erasure fallback. Lossless captures reproduce all comparisons. Every actual public support root is included; the complete original-parent capture is also retained.
* **Kernel coverage:** all eight new modules and the exact changed import root passed fresh frozen replay. All 1,026 preceding mathematical sources and complete kernel-data artifacts match the pinned preceding verified checkpoint byte for byte. This chain covers all 1,035 modules; it does not claim a fresh full-library replay.
* **Source provenance:** five whole modules and five complete blueprint chapters reproduce from fixed normal published Git. Three pure supports preserve three complete original prerequisites and their recorded original contexts. Exactly two recorded whole-module import changes expose those prerequisites; original statement and proof text is unchanged. Independent source/context review covers the entire recovered proofs and scope. The initial missing-prerequisite build failure is retained.
* **Blueprint scope:** 415 synchronized complete chapters contain 1,593 complete proofs, with 4,335 distinct local bindings, 241 verified upstream-only bindings and two explicitly unresolved historical attachment names. The new labelled definition is counted separately from its 12 accompanying proved nodes. The full document includes 500 chapters, 2,064 proof environments and 5,494 local bindings. Its [812-page PDF]({link}/blueprint-pdf-build/extensions.pdf) compiles without LaTeX errors; inherited reference/bookmark warning inventories are unchanged.
* **Previously disclosed parser outputs:** the earlier native280 publication separately audited three generated front-end definitions of a local notation. Their relocated generated names and quoted hygiene identifiers differ, so its raw all-1,009-root comparison remains explicitly `BLOCKED_EXACT_DIFFERENCE`; equality of those three bodies remains unclaimed. Their source-generation evidence and full axiom/kernel coverage remain included through the verified predecessor chain. This increment has no unmatched new front-end roots.

Reproduce the normal Git source and complete recorded expressions with:

```sh
python3 {link}/verify_incremental_source.py --source-root /path/to/archon-nakamaye
python3 {link}/verify_recorded_full_expressions.py
```

Source replay, build, actual-root axiom audit, captured-expression comparison and frozen kernel replay are separate gates. The [preceding verification](audit/analytic-strict-generators-and-coupled-global-endpoint-20261018/verification.md) retains its complete evidence and earlier parser disclosures. G5, G6 and G7 remain closed; G1, G2, G3, G4, G8 and G9 retain the outstanding general goals listed above.

'''+s[stop:]
assert '**Three of the nine original gaps are closed: G5, G6 and G7.**' in s
(A/'README-next-checkpoint.md.txt').write_text(s);(ROOT/'README.md').write_text(s)
print('README_UPDATED_FIXED338_VERIFIED_SCOPE')
