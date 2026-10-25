# Current scope

## De Jong alterations over arbitrary fields

The proved native alteration theorem is integrated through the local package
[`vendor/DeJongAlterations`](vendor/DeJongAlterations). Its original native
producer sources are extracted from source commit
`187095a1888ecadb1f365e6d4dc0cb75dcd61eff`, preserving their bytes and
contributor/license headers. The proof sources are included in this repository;
building the integration does not require access to the private source repository.
`Hironaka.deJongAlterationTheorem` has only `(k : Type u) [Field k]` as inputs;
`Hironaka.exists_alterationWithBoundary` specializes it to an actual variety and
prescribed proper closed subset. Both are available from `import Hironaka.DeJong`
and the full `import Hironaka`.

The output retains the original variety, genuine alteration, regular projective
compactification and the whole strict SNC boundary, with its exact prescribed
support. Geometric integrality and perfectness are not assumed. The separate
perfect-field generically-étale refinement and other independent paper results
are outside this integration. See [the API and source provenance](docs/DEJONG.md).
Combined-build and recursive-axiom verification for this integration is recorded
in [its verification receipt](audit/dejong-integration-20261023/validation.json).
The earlier analytic verification numbers below describe their own checkpoints.

## Standalone complex-analytic scope

The table below describes the standalone analytic export at the fixed
[fourteen-module checkpoint](https://github.com/MingchenXia/hironaka/commit/668ccdac96b962a30f2f12fff2b3f4fbda20ef75),
whose native source is
[`eef2a728`](https://github.com/MingchenXia/archon-nakamaye/commit/eef2a7286318c05dda607a2909399937ccaa4c27).

The separately advanced native repository records five closed original
goals (G2, G5, G6, G7 and G9) at
[checkpoint546](https://github.com/MingchenXia/archon-nakamaye/blob/c04efdbe221bdf608588adb87f66553951acb75c/TranscendentalNakamaye/audit/hironaka-original-tangent-symbols-20261023/all-nine-continuation-plan.json).
Those later native producers are not part of this standalone export;
G9 remains open in the exported scope described here.

Four original gaps are closed in this export: **G2, G5, G6 and G7**. General
**G1, G3, G4, G8 and G9 remain open**. These labels describe mathematical scope.

| Gap | Status and scope |
|---|---|
| G1 — categories | Open. A specified intrinsic isomorphism of reduced analytic models gives a genuine stable ambient comparison with the same point map. Canonical stabilization, abstract embedding independence and proper resolution descent remain. Separately verified characteristic-zero algebraic strong/functorial endpoints do not complete the analytic-space goal. |
| G2 — canonical elementary resolution | Closed at its original elementary-morphism scope: principalization, irreducible, pure, own dimension-part, mixed and separation families, including compact and local forms and genuine smooth Cartesian comparisons. |
| G3 — noncompact global construction | Open. Smooth-curve and compact-component histories, discrete full-value cut scheduling, and proper limits, finite-stage factors and actual centre-relative limit strict transforms of given locally finite histories are proved. Unrestricted noncompact scheduling remains. |
| G4 — sharp resolution | Open. The original smooth-curve case is complete. Arbitrary-dimensional incident-centre residual geometry and genuine finite dynamic prefixes retain the whole boundary and ideal factors. Actual finite dynamic prefixes avoid the original good locus, and the first canonical window has a strict full-invariant drop. Recursive current-open value comparisons, termination and general global scheduling remain. |
| G5 — dimension components | Closed. Each dimension part is exactly the union of the genuine global irreducible components of that dimension. |
| G6 — complete SNC divisor sums | Closed. Finite and locally finite sums use actual global coefficients and whole local ideal equality, including disconnected boundary members and zero coefficients. |
| G7 — simultaneous normal crossings | Closed. The resolved smooth strict transform is transverse to the entire accumulated SNC boundary. |
| G8 — Hilbert–Samuel transformation | Open. In zero-direction point charts, the complete original/current HS profiles agree iff every member retains its original vertex order, using the same canonical normalized family chosen before either premise. Arbitrary-direction source stability is now derived internally from original point persistence, and weighted coefficient tracking uses the same family. The actual relative image family has whole initial generation and all-colon compression. General permissible-centre HS compatibility, relative maximal standardness and the history driver remain. |
| G9 — general NC input | Open. For an adapted NC carrier and retained SNC boundary, coherent ideal, positive marking and compact cosupport give an actual finite prephase and an open containing the entire current cosupport where the old trace is smooth, transverse to the whole boundary and SNC with it. A compact prephase globalizes its whole adapted terminal pair. Labelled NC boundaries preserve original positions under transport and explicit regrouping; highest-branch permissions are proved. Global old-branch history tracking and the canonical general-NC driver remain. |

## Meaning of G2 completion

The canonical object is the actual resulting elementary morphism. The proved
families supply its genuine terminal target and comparisons with arbitrary
independent intrinsic smooth-source constructions, including identity and
composition of the actual Cartesian maps. Local forms retain prescribed opens
or choose one neighbourhood before all source comparisons.

A globally functorial sequence indexed by natural numbers, sharp preservation
of the original NC good locus, and general self-intersecting NC input remain
separate G3, G4 and G9 goals; they are outside the G2 completion claim.

The exact source-family audit covers 75 original declarations in 18 files;
[the accepted native completion record](https://github.com/MingchenXia/archon-nakamaye/blob/4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07/TranscendentalNakamaye/audit/hironaka-all-nine-phase2-20261020/completion-145/g2-completion-145.json)
records the full mapping and checks.

## Verification and source

The fixed native increment underlying this export contains 14 independently checked modules,
324 actual compiled-root observations, 52 complete proof nodes and six
geometric definitions. Its bounded aggregate passes 5,657 warm build jobs.
These are native verification metrics.

The standalone export adds the same 14 whole modules and proof chapters,
plus eight complete original auxiliary declarations in three support modules.
At that standalone checkpoint the full build passed 5,707 jobs with zero
warnings; all 81 local blueprint bindings resolved. Its public axiom check
covered 14,001 declarations.

[The current verification receipt](audit/phase5-original-producers-20261021/publication-verification.json)
records source replay, exact new-module kernel checks, actual compiled-payload
axiom checks and full mathematical-expression comparisons. Generated notation
has separate typed/source and no-logical-dependent checks; raw structural
differences remain recorded, and parser-body equality is not claimed.
The previous [checkpoint](audit/phase4-semantic-producers-20261021/publication-verification.json)
and accepted mathematical sources remain unchanged.

The [source-only integration record](audit/phase5-main-integration-20261025/mechanical-source-verification.json)
separately checks this fixed export against the newer de Jong main.
A combined build of the reconciled graph is pending; the historical
receipts above do not claim that combined validation.

Two complete modules, `HironakaOriginalGlobalOffZero` and
`HironakaOriginalGlobalProperModification`, remain deferred because an existing
standalone dependency has a different stored theorem type. Their complete
source, blueprint chapters and blocked comparisons are retained in the audit.
No claim is made that those two modules were synchronized.

See [the public API](docs/API.md) for original geometric statements and
[the blueprint](blueprint/extensions.tex) for mathematical proofs.
