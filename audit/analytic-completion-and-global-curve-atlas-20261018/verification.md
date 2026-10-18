# Fixed native313 public increment

This increment copies the accepted native **313-module** checkpoint
`879b6a01452b3d57b502d3f3568df2876f816d66` from normal published revision
`7266ce19c9d3f79a8693f7ded964755af7af59a7` (upstream PR111), beyond public
base `7077e5469e0d6a5ce3a95e51b5e7400dc2d906ec`. Later native checkpoints
are excluded. [The final receipt](final-validation.json) checks the current
source and installed artifacts against each frozen verification gate.

The new mathematics identifies the genuine analytic germ ring's adic completion,
proves faithful flatness of its original Taylor map, recovers original analytic
syzygies and whole-ideal intersections, constructs analytic exceptional quotients
from finite coefficient data, proves full GENERAL comparisons on the stated
given smooth histories after one admissible preparation step, and constructs a
proper global complex endpoint for original smooth curves with indexed SNC
boundary geometry and an isomorphism over the whole original good locus.
The exact hypotheses remain in the complete original statements and blueprints.
G5, G6 and G7 remain closed; G1, G2, G3, G4, G8 and G9 retain their general gaps.
In particular this checkpoint does not identify the conventional global strict
closure or construct the complete global blowup schedule for that curve endpoint.

## Source and independent review

* [Normal published source replay](published-source-replay.json) reconstructs all
  **33 whole original modules**, **33 complete blueprint chapters**, **76 complete
  blueprint proofs**, and **175 new distinct local declaration bindings**.
  Only eight recorded imports are added to the public import root. All **968
  preceding mathematical sources remain byte-identical** to the public base.
* [The pure support inventory](new-support-provenance.json) recovers three complete
  original admissibility proofs in one additive module. Their complete original
  Generic and Masked contexts, all imports/opens, intervening contexts and original
  scope closures are retained. Compiler source ranges and raw declaration sidecars
  are bound to the fixed normal published source. No proof/type tokens are omitted.
* [Two instance-context restorations](original-instance-context-provenance.json)
  select the original `SubsemiringClass.toAddSubmonoidClass` path locally on two
  new declarations. The original theorem statements, proof bodies, documentation
  and entire owning preludes are unchanged. Initial nonmatching captures remain
  preserved; the final strict gate verifies the complete compiled values.
* G3 independently read the [entire support and its contexts](g3-member-lower-admissibility-original-support-review.md)
  and [both instance-context restorations](g3-original-instance-context-delta-review.json),
  checked original ranges and byte guards, and reviewed the complete strict reports.

`verify_incremental_source.py --source-root /path/to/archon-nakamaye` uses normal
published Git only. It needs no private ledger, source rebuild or remote request.
The namespace relocation function, AllV2 and ScopedOwnersV3 serializers, and full
structural comparator remain frozen under [their original hashes](frozen-tool-profiles.json).

## Build, actual roots and complete expressions

* [Final `lake --wfail build`](build-03-original-subsemiring-instance-contexts.log):
  **4,994 jobs, zero warnings**.
* [All actual-root and binding audit](all-actual-roots-final.log): **1,002
  mathematical modules plus the import root**, **16,863 actual compiled roots**,
  including private/generated helpers, use only `propext`, `Classical.choice` and
  `Quot.sound`. All **175 new**, **4,249 synchronized**, and **5,408 full-document**
  distinct local binding spellings resolve with zero missing bindings.
* [All 33 whole modules](whole-module-full-expression-comparison.json): **289/289
  actual roots** have exactly matching full types and values under unchanged
  ScopedOwnersV3. [The pure support](fragment-full-expression-comparison.json):
  **3/3 actual roots** match under unchanged AllV2. Together these include **241
  complete theorem proofs**. Missing roots, extra roots, differences, fallback
  comparisons, skipped auxiliaries, numeric/binder erasures and alpha/definitional
  equivalence allowances are all zero. Metadata and full Name components remain.
* The AllV2 source-parent capture contains eight roots because the original module
  also has five declarations outside this three-proof extraction. [The selection
  receipt](fragment-original-root-selection.json) retains all eight original rows
  and selects the exact three original keys of **every** actual public support root
  as verbatim complete rows. No public root is filtered or omitted. The initial
  unselected-parent comparison is retained as correctly blocked by those five extras.
* [Lossless gzip captures](recorded-full-expression-captures.json) retain the final
  complete snapshots, initial failed public snapshot, and complete original support
  parent. `verify_recorded_full_expressions.py` reproduced both complete comparisons
  and [passed all 292 roots and 241 theorem proofs](recorded-full-expression-replay.log).

The preceding PR7 checkpoint's separate disclosure remains unchanged: **1,006
mathematical/private/generated mathematical roots** were strictly compared, while
**three generated front-end definitions** were independently audited through typed
source generation. Its raw all 1,009 structural comparison remains
`BLOCKED_EXACT_DIFFERENCE`, owing to relocated generated names and quoted hygiene
identifiers. Structural equality of those three bodies is unclaimed. Their source,
axiom and kernel coverage is retained through the verified predecessor chain.
This 313 increment has **zero unmatched new front-end roots**.

## Frozen kernel coverage

[Fresh installed LeanChecker replay](incremental-kernel-replay.json) passed all
**34 new modules** and separately the changed **`Hironaka` import root** in 157.897
seconds with one Lean thread. Exact complete source, kernel-data and compiler-import
metadata snapshots remained unchanged before and after replay. The actual replayed
module inventory equals the complete new target inventory.

[The pinned predecessor guard](previous-frozen-kernel-data-reuse.json) verifies
all **968 preceding sources and complete kernel-data artifacts** against the
committed PR7 snapshots/receipt. No preceding kernel artifact changed or required
additional replay. This gives explicit coverage of all **1,003 local modules**;
it does not claim a fresh full-library replay. Final validation also rehashes all
current sources, installed kernel parts and `.ilean` metadata against the frozen
post-replay snapshot.

## Complete blueprint and PDF

[Source and PDF validation](blueprint-validation.json) checks the union of complete
synchronized chapters, with overlapping binding spellings counted once. **390
synchronized chapters retain 1,541 complete original proofs** and reference **4,249
distinct compiled local bindings**, **241 verified upstream-only bindings** and
**two explicitly unresolved historical names**. The new 175 local bindings are
disjoint from the previous 4,074. Historical unresolved names remain unverified.

The full master document includes **475 unique chapters**, **2,012 complete proof
environments** and **5,408 distinct local binding spellings**. All inputs exist;
all **442 preceding input chapter sources** remain byte-identical. The master
changes only its recorded synchronized-scope paragraph and the 33 added inputs.

Three LaTeX passes produce the stable [786-page PDF](blueprint-pdf-build/extensions.pdf)
(3,965,579 bytes), with zero LaTeX errors or pending cross-reference reruns. All 476
master/input source hashes are unchanged during rendering and checked again by
final validation. The preceding warning inventories are retained: 704 LaTeX
warnings (703 reference warnings and one amsmath warning), six bookmark warnings,
and 72 missing PDF destinations. No statement, proof or historical label was
rewritten to suppress these warnings.

## Reproduction

```sh
python3 audit/analytic-completion-and-global-curve-atlas-20261018/verify_incremental_source.py --source-root /path/to/archon-nakamaye
python3 audit/analytic-completion-and-global-curve-atlas-20261018/verify_recorded_full_expressions.py
python3 audit/analytic-completion-and-global-curve-atlas-20261018/validate_publication.py
```

The source replay needs the pinned normal published Git revision. Captured-expression
reproduction needs only the committed lossless captures and unchanged comparator.
Final validation additionally requires this checkpoint's built Lean artifacts; it
launches no build, export or kernel replay. The separate retained scripts perform
fresh exports and fresh kernel replay when the single heavy slot is available.
