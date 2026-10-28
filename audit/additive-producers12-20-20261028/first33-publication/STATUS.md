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

The table below describes the standalone analytic export, including 29 additional
whole modules and four original support modules from fixed native source
[`53bb34a4`](https://github.com/MingchenXia/archon-nakamaye/commit/53bb34a4a1607f358638012e2d9cb1d27818ca91).
The earlier
[fourteen-module checkpoint](https://github.com/MingchenXia/hironaka/commit/668ccdac96b962a30f2f12fff2b3f4fbda20ef75)
is retained unchanged.

The separately advanced [native checkpoint](https://github.com/MingchenXia/archon-nakamaye/commit/6ae2122a9cf82f1469b68fe41e8e6cf115075d6a)
has five closed goals (G2, G5, G6, G7 and G9); its 67-module increment
is not exported here, where G9 remains open.

Four original gaps are closed in this export: **G2, G5, G6 and G7**. General
**G1, G3, G4, G8 and G9 remain open**. These labels describe mathematical scope.

| Gap | Status and scope |
|---|---|
| G1 — categories | Open. A specified intrinsic isomorphism of reduced analytic models gives a genuine stable ambient comparison with the same point map. Coherent normal stabilization has an exact initial depth-shift law; matched actual blowup charts retain whole nonradical controlled ideals. Canonical finite-history stabilization, abstract embedding independence and proper resolution descent remain. Separately verified characteristic-zero algebraic strong/functorial endpoints do not complete the analytic-space goal. |
| G2 — canonical elementary resolution | Closed at its original elementary-morphism scope: principalization, irreducible, pure, own dimension-part, mixed and separation families, including compact and local forms and genuine smooth Cartesian comparisons. |
| G3 — noncompact global construction | Open. Smooth-curve and compact-component histories, discrete full-value cut scheduling, and proper limits, finite-stage factors and actual centre-relative limit strict transforms of given locally finite histories are proved. Compact-exhaustion escape characterizes local finiteness; saturated windows give analytic gluing and compatible local proper maps give a global proper map. An unrestricted escaping blowup scheduler remains. |
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

The [additional producer verification](audit/disjoint-producers-20261028/publication-verification.json)
records 33 new physical modules: 29 whole original modules and four support
modules containing seven complete original auxiliary declarations. Their types
and entire proof values pass strict expression comparison with the fixed native
sources. The export includes 26 whole original blueprint chapters and ten
additional support proofs, for 100 complete written proofs and 209 literal
bindings. Every new physical module has an independent exact kernel check and
an audit of all its actual declaration types and whole proof values; 3,678
guarded existing files remain byte-identical. Historical failed comparisons and
the inherited broad-build warning log are retained separately in that audit.
These prerequisites do not close another original gap.

The earlier fixed native increment contains 14 independently checked modules,
324 actual compiled-root observations, 52 complete proof nodes and six
geometric definitions. Its bounded aggregate passes 5,657 warm build jobs.
These are native verification metrics.

The standalone export adds the same 14 whole modules and proof chapters,
plus eight complete original auxiliary declarations in three support modules.
At that standalone checkpoint the full build passed 5,707 jobs with zero
warnings; all 81 local blueprint bindings resolved. Its public axiom check
covered 14,001 declarations.

[That checkpoint's verification receipt](audit/phase5-original-producers-20261021/publication-verification.json)
records source replay, exact new-module kernel checks, actual compiled-payload
axiom checks and full mathematical-expression comparisons. Generated notation
has separate typed/source and no-logical-dependent checks; raw structural
differences remain recorded, and parser-body equality is not claimed.
The previous [checkpoint](audit/phase4-semantic-producers-20261021/publication-verification.json)
and accepted mathematical sources remain unchanged.

The [combined integration verification](audit/phase5-main-integration-20261025/publication-verification.json)
records the actual rebuild of both libraries under main's unchanged
configuration, followed by the default build, test and 83 current bindings.
Its test checks 48,147 registered names with standard axioms;
vendor warning logs are retained. The 17 historical kernel checks are
reused only after exact identity of their rebuilt kernel artifacts.

Two complete modules, `HironakaOriginalGlobalOffZero` and
`HironakaOriginalGlobalProperModification`, remain deferred because an existing
standalone dependency has a different stored theorem type. Their complete
source, blueprint chapters and blocked comparisons are retained in the audit.
No claim is made that those two modules were synchronized.

See [the public API](docs/API.md) for original geometric statements and
[the blueprint](blueprint/extensions.tex) for mathematical proofs.
