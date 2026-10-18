# Hironaka

A Lean 4 / Mathlib formalization of **resolution of singularities in complex-analytic geometry**: principalization of coherent ideal sheaves and embedded resolution of analytic subsets of complex manifolds, by finite sequences of blowups with smooth centres, together with the canonical resolution of marked ideals from which both are derived (in the style of Włodarczyk and Bierstone--Milman).

The original library was produced by AI agents (Claude). Subsequent continuation modules are credited in their file headers. The formalization is checked by Lean's kernel; see [Verification](#verification).

## Current status — 18 October 2026

The checked library contains **1,002 mathematical modules**, plus the `Hironaka` import root. All **16,863 actual compiled declarations**, including private and generated declarations, depend only on the three standard axioms. The [verification receipt](audit/analytic-completion-and-global-curve-atlas-20261018/final-validation.json) records fresh frozen kernel replay of all 34 added modules and the import root. All 968 preceding mathematical sources and their complete kernel-data artifacts remain byte-identical to the verified preceding checkpoint.

The latest completed subgoals identify the actual analytic germ ring's adic completion and prove faithful flatness of its genuine Taylor map, construct analytic exceptional quotients from finite coefficient data, compare original prepared values on the same given smooth histories, and construct a proper global complex endpoint with indexed SNC geometry for original smooth curves. These results advance G2, G4 and G8; the remaining general goals are stated below.

**Three of the nine original gaps are closed: G5, G6 and G7.** The other six have the remaining general statements listed below; several already have substantial completed cases. These are scope labels, not a numerical measure of proof difficulty or completion.

| Closed gap | What is proved | Lean evidence |
|---|---|---|
| G5 — dimension components | Every dimension part is exactly the union of the genuine global irreducible components of that dimension, with finite local branch filtering. | [`dimensionPart_eq_sUnion_globalComponents`](Hironaka/Resolution/HironakaDimensionGlobalComponents.lean) |
| G6 — complete SNC divisor sums | Finite sums for compact support and locally finite sums for arbitrary support, using one global coefficient function and full local ideal equality; disconnected members and zero coefficients are covered. | [`HironakaCompleteDivisorSum`](Hironaka/Resolution/HironakaCompleteDivisorSum.lean), [`HironakaLocallyFiniteDivisorSum`](Hironaka/Resolution/HironakaLocallyFiniteDivisorSum.lean) |
| G7 — simultaneous normal crossings | The resolved strict transform is transverse to the entire accumulated SNC boundary; generic upgrade lemmas and strengthened existence theorems retain the original conclusions. | [`HironakaNormalCrossingsTransversality`](Hironaka/Resolution/HironakaNormalCrossingsTransversality.lean) |

**Six broader gaps remain open:**

| Direction | Remaining source-facing goal |
|---|---|
| G1 — categories | Resolution for abstract analytic spaces and the characteristic-zero algebraic setting, beyond the present complex-manifold setting. |
| G2 — canonical elementary resolution | General higher-dimensional original invariants, complete value and history compatibility, descent and termination. |
| G3 — noncompact global construction | Produce actual global centres, exhaustion scheduling and compact-uniform stabilization, then identify and glue the terminal analytic space in general dimension. |
| G4 — sharp resolution | Construct the complete defect invariant and prove its decrease and termination in general dimension; identify the conventional global strict transform and geometric blowup history beyond the proved proper global smooth-curve endpoint. |
| G8 — Hilbert–Samuel transformation | General permissible-centre vertex compatibility, transformed presentations and stability, Bennett inequalities, and the full analytic/formal strict-transform bridge. |
| G9 — general NC input | Connect local branches and self-intersections of general normal-crossings input to the canonical driver and additional-ideal compatibility. |

The current proof fronts are general canonical history comparisons, the remaining global strict-transform and history identifications for smooth curves, and general Hilbert–Samuel transformation. Research plans are not counted as completed Lean proofs. The detailed [gap status](#status-of-the-nine-original-gaps) separates completed gaps, completed cases and the remaining general statements.

## Setting

All statements are about complex manifolds of dimension `n`, given unbundled:

```lean
{X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
```

where `ComplexModel n = EuclideanSpace ℂ (Fin n)` and `IsComplexManifold n X` asks for a Hausdorff, second countable topological space with a holomorphic atlas (Mathlib's `IsManifold 𝓘(ℂ, ℂⁿ) ∞`). Everything is complex-analytic. The original global finite-sequence existence theorems assume **compactness**: either `X` is compact, or the relevant set (`Z(𝔞)`, `V`, `W`) is compact; otherwise the results hold over open sets contained in a compact set, or over a **relatively compact** neighbourhood of any compact set.

Vocabulary (all in this library): `GermIdeal n X` is an ideal sheaf of holomorphic germs, with `IsCoherent`, `zeroLocus` (`Z(𝔞)`), `pullback`; `EffectiveDivisor` is an invertible ideal sheaf `𝒪(-D)` with its support; `ClosedIrreducibleAnalyticSubvariety` and `IsComplexAnalyticSubset` are analytic subsets; `Hironaka.singularLocus V = V \ V_reg` (`V_sing`), and `W_sing = W \ regularLocus W d`; `IsSNCDivisor n E` says that the closed members of the list `E` have simple normal crossings (at every point the members through it are distinct coordinate hyperplanes of one chart); an *admissible blowup sequence* of `(X, E₀)` over `F` (`HironakaAdmissibleSequence.IsAdmissibleBlowupSequence n X E₀ F X' f E`) is a finite composition `f : X' → X` of blowups with smooth centres, each centre having only normal crossings with the divisor accumulated so far and lying over `F`; `E` starts with the strict transforms of the members of `E₀`, then has one member per blowup. `exceptionalLocus` (`Exc f`), `strictTransform` and `IsIsomorphismOver` have their usual meaning.

## What is proved

The original API surface consists of the 42 theorems of the modules `Hironaka.API`, `Hironaka.API2`, `Hironaka.API3`, `Hironaka.API4`. They are restatements, with the internal machinery hidden, of the theorems of the `Hironaka.Resolution.*` modules. All of them are stated in the namespace `Hironaka`.

The principalization hypothesis "`𝔞` is nonzero at every point" is written out as `∀ x, ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0` (at every point some germ of `𝔞` does not vanish identically near the point).

### `Hironaka.API`

| theorem | statement |
|---|---|
| `Hironaka.forall_isNonzeroAlongAt_univ_iff` | the internal predicate `IsNonzeroAlongAt univ 𝔞 x` for all `x` ⟺ `∀ x, ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0`. |
| `Hironaka.exists_principalization` | `X` compact, `𝔞` coherent, nonzero at every point: admissible sequence of `(X, [])` over `Z(𝔞)`, effective `D` with `f^*𝔞 = 𝒪(-D)`, `E` SNC, `Supp D = ⋃E = f⁻¹Z(𝔞)`, `f` iso over `X \ Z(𝔞)`. |
| `Hironaka.exists_principalization_of_isCompact` | the same on any `X` with `Z(𝔞)` compact. |
| `Hironaka.exists_principalization_of_subset_isCompact` | the same for `𝔞\|X₀` over any open `X₀` contained in a compact set. |
| `Hironaka.exists_principalization_local` | for compact `K`: a relatively compact open `U ⊇ K` and the same over `U`. |
| `Hironaka.exists_principalization_boundary` | `Z(𝔞)` compact, `E₀` SNC: admissible sequence of `(X, E₀)` over `Z(𝔞)`, `E` SNC, `f^*𝔞 = 𝒪(-D)`, `Supp D = ⋃ E.drop \|E₀\| = f⁻¹Z(𝔞)`, `f` iso over `X \ Z(𝔞)`. |
| `Hironaka.exists_embeddedResolution` | `X` compact, `V` closed irreducible: admissible sequence of `(X, [])` over `V_sing`, `E` SNC, `Exc f = ⋃E = f⁻¹(V_sing)`, `f` iso over `X \ V_sing`, strict transform a closed connected submanifold of dimension `dim V`, normal crossings with `E`. |
| `Hironaka.exists_embeddedResolution_of_isCompact` | the same on any `X` with `V` compact. |
| `Hironaka.exists_embeddedResolution_of_subset_isCompact` | over any open `X₀` contained in a compact set (strict transform of `V ∩ X₀` a closed submanifold, dimension `dim V` at each point; not claimed connected). |
| `Hironaka.exists_embeddedResolution_pure` | `X` compact, `W` analytic of pure dimension `d < n` (`W ⊆ closure (Reg_d W)`), possibly reducible: as for `V` with `W_sing`, strict transform closed submanifold of dimension `d` at each point (possibly disconnected). |
| `Hironaka.exists_embeddedResolution_pure_of_isCompact` | the same on any `X` with `W` compact. |

### `Hironaka.API2`

| theorem | statement |
|---|---|
| `Hironaka.not_le_vanishingIdeal_univ` | if some germ of `𝔞` is not identically zero near its point, `𝔞 ⊄ 𝓘_X`. |
| `Hironaka.exists_principalization_of_connected` | `X` compact and connected, `𝔞` coherent with some germ not identically zero: the conclusion of `exists_principalization`. |
| `Hironaka.exists_principalization_boundary_of_compactSpace` | `X` compact, `E₀` SNC: the conclusion of `exists_principalization_boundary`. |
| `Hironaka.exists_principalization_boundary_of_subset_isCompact` | any `X` (no compactness of `Z(𝔞)`), `E₀` SNC, over an open `X₀` contained in a compact set, relative to `E₀\|X₀`: admissible sequence of `(X₀, E₀\|X₀)` over `Z(𝔞) ∩ X₀`, `E` SNC, `f^*(𝔞\|X₀) = 𝒪(-D)`, `Supp D = ⋃ E.drop \|E₀\| = f⁻¹(Z(𝔞) ∩ X₀)`, `f` iso over `X₀ \ Z(𝔞)`. |
| `Hironaka.exists_principalization_boundary_local` | the same over a relatively compact open neighbourhood `U` of a compact `K`. |
| `Hironaka.exists_embeddedResolution_local` | any `X`, `V` irreducible, `K` compact: a relatively compact open `U ⊇ K` and the conclusion of `exists_embeddedResolution_of_subset_isCompact` over `U`. |
| `Hironaka.exists_embeddedResolution_pure_of_subset_isCompact` | `W` of pure dimension `d < n` (not compact), over any open `X₀` contained in a compact set. |
| `Hironaka.exists_embeddedResolution_boundary_of_isCompact` | `W` compact analytic of pure dimension `d < n`, `E₀` SNC with `W ⊆ closure (W \ \|E₀\|)`, `F = W_sing ∪ (W ∩ \|E₀\|)`: admissible sequence of `(X, E₀)` over `F`, `E` SNC, `Exc f ⊆ ⋃ E.drop \|E₀\| ⊆ f⁻¹F`, `f⁻¹(W_sing) ⊆ Exc f`, `f` iso over `X \ F`, strict transform closed submanifold of dimension `d` at each point with normal crossings with `E`. |
| `Hironaka.exists_embeddedResolution_boundary` | the same with `X` compact. |
| `Hironaka.exists_embeddedResolution_boundary_of_subset_isCompact` | the same for any `W` over an open `X₀` contained in a compact set, relative to `E₀\|X₀`. |
| `Hironaka.exists_embeddedResolution_boundary_local` | the same over a relatively compact open neighbourhood `U` of a compact `K`. |
| `Hironaka.eq_iUnion_dimensionPart` | an analytic `W` is `⋃_{k ≤ n} W⁽ᵏ⁾`, `W⁽ᵏ⁾ = dimensionPart W k = closure (Reg_k W)`. |
| `Hironaka.isComplexAnalyticSubset_dimensionPart` | `W⁽ᵏ⁾` is analytic and of pure dimension `k`. |
| `Hironaka.exists_embeddedResolution_dimensionPart_of_isCompact` | `W` compact analytic (components of any dimensions), `k < n`: the conclusion of `exists_embeddedResolution_pure_of_isCompact` for `W⁽ᵏ⁾` (its own sequence). |
| `Hironaka.exists_embeddedResolution_dimensionPart` | the same with `X` compact. |
| `Hironaka.exists_embeddedResolution_dimensionPart_boundary_of_isCompact` | the boundary form for `W⁽ᵏ⁾`. |
| `Hironaka.canonicalResolution` | `X : CMfd n` compact, `𝔪` a marked ideal of the domain: a resolution `T` that is a canonical segment for the canonical invariant, the invariant USC along canonical segments, `T` restricts to canonical segments on opens, and every canonical resolution of `Φ^*𝔪` (`Φ` a biholomorphism) is isomorphic to `T` over `Φ`. |

### `Hironaka.API3`

| theorem | statement |
|---|---|
| `Hironaka.exists_embeddedResolution_analytic_of_isCompact` | `W` compact analytic, `interior W = ∅`, components of any dimensions: ONE admissible sequence of `(X, [])` over `W_sing`, `E` SNC, `Exc f = ⋃E = f⁻¹(W_sing)`, `f` iso over `X \ W_sing`, `W'` a closed submanifold, `W' = ⋃_{k<n} W'⁽ᵏ⁾`, the `W'⁽ᵏ⁾` pairwise disjoint, `W'` of dimension `k` at each point of `W'⁽ᵏ⁾`, `W'` NC with `E`. |
| `Hironaka.exists_embeddedResolution_analytic` | the same with `X` compact. |
| `Hironaka.exists_embeddedResolution_analytic_boundary_of_isCompact` | relative to `E₀` SNC with `W ⊆ closure (W \ \|E₀\|)`, `F = W_sing ∪ (W ∩ \|E₀\|)`: admissible sequence of `(X, E₀)` over `F`, `E` SNC, `Exc f ⊆ ⋃ E.drop \|E₀\| ⊆ f⁻¹F`, `f⁻¹(W_sing) ⊆ Exc f`, iso over `X \ F`, `W'` as above, NC with `E`. |
| `Hironaka.exists_embeddedResolution_analytic_boundary` | the same with `X` compact. |
| `Hironaka.exists_separation` | `A, B` analytic, `interior A = ∅`, `A ∩ B` compact, `A ⊆ closure (A \ B)`, `B ⊆ closure (B \ A)`, `E₀` SNC: admissible sequence of `(X, E₀)` over `A ∩ B` (principalization of `𝓘_A + 𝓘_B`), `E` SNC, strict transforms of `A` and `B` disjoint. |
| `Hironaka.isAdmissibleBlowupSequence_comp` | `f` admissible for `(X, E₀)` over `F` with divisor `E`, `g` admissible for `(Y, E)` over `f⁻¹F`: `f ∘ g` admissible for `(X, E₀)` over `F`. |
| `Hironaka.isIsomorphismOver_compl_of_isAdmissibleBlowupSequence` | an admissible sequence over `F` is an isomorphism over `X \ F`. |
| `Hironaka.exceptionalLocus_subset_of_isAdmissibleBlowupSequence` | `Exc f ⊆ ⋃ E.drop \|E₀\| ⊆ f⁻¹F` for every admissible sequence over `F`. |

### `Hironaka.API4`

| theorem | statement |
|---|---|
| `Hironaka.exists_embeddedResolution_analytic_of_subset_isCompact` | `W` analytic, `interior W = ∅`, components of any dimensions, `X₀ ⊆ K` compact: ONE admissible sequence of `(X₀, [])` over `W_sing ∩ X₀`, `E` SNC, `Exc f = ⋃E = f⁻¹(W_sing ∩ X₀)`, iso over `X₀ \ W_sing`, `W'` (strict transform of `W ∩ X₀`) a closed submanifold, `W' = ⋃_{k<n} W'⁽ᵏ⁾` (strict transforms of `W⁽ᵏ⁾ ∩ X₀`), pairwise disjoint, `W'` of dimension `k` along `W'⁽ᵏ⁾`, NC with `E`. |
| `Hironaka.exists_embeddedResolution_analytic_local` | the same over a relatively compact open neighbourhood `U` of a given compact set. |
| `Hironaka.exists_embeddedResolution_analytic_boundary_of_subset_isCompact` | relative to `E₀` SNC with `W ⊆ closure (W \ \|E₀\|)`, `F = W_sing ∪ (W ∩ \|E₀\|)`: admissible sequence of `(X₀, E₀\|X₀)` over `F ∩ X₀`, `E` SNC, `Exc f ⊆ ⋃ E.drop \|E₀\| ⊆ f⁻¹(F ∩ X₀)`, `f⁻¹(W_sing ∩ X₀) ⊆ Exc f`, iso over `X₀ \ F`, `W'` as above, NC with `E`. |
| `Hironaka.exists_embeddedResolution_analytic_boundary_local` | the same over a relatively compact open neighbourhood of a compact set. |
| `Hironaka.exists_separation_of_subset_isCompact` | `A, B` analytic, `interior A = ∅`, `A ⊆ closure (A \ B)`, `B ⊆ closure (B \ A)` (NO compactness of `A ∩ B`), `E₀` SNC, `X₀ ⊆ K`: admissible sequence of `(X₀, E₀\|X₀)` over `A ∩ B ∩ X₀`, `E` SNC, strict transforms of `A ∩ X₀`, `B ∩ X₀` disjoint. |
| `Hironaka.exists_restrict_opens` | `f` admissible for `(X, E₀)` over `F` with divisor `E`, `O ⊆ X` open: `f'` admissible for `(O, E₀\|O)` over `F ∩ O` with divisor `j⁻¹E`, `j : Y' → Y` holomorphic open embedding without exceptional points onto `f⁻¹(O)`, `f ∘ j = f'`, `Exc f' = j⁻¹ Exc f`, strict transform of `S ∩ O` by `f'` = `j⁻¹` (strict transform of `S` by `f`). |

The underlying statements in terms of towers of blowups are part of the library as well: `Hironaka.HironakaAdmissibleSequence.exists_tower_embedded_of_isCanonical`, `Hironaka.HironakaEmbeddedBoundary.exists_tower_embedded_of_isCanonical`.

## Extensions added on 11 October 2026

The four extension modules exported by `import Hironaka` add 40 named mathematical declarations (38 theorems and two definitions). The original 42 API statements and proofs are unchanged.

| namespace | additions |
|---|---|
| `Hironaka.HironakaDimensionGlobalComponents` | Nine declarations identify `dimensionPart A k` exactly with the union of genuine global irreducible components of pure geometric dimension `k`, prove the purity dictionary, and construct finite filtered local decompositions. No compactness, empty-interior or positive-dimension assumption is needed for the identification. |
| `Hironaka.HironakaNormalCrossingsTransversality` | Four geometric upgrade lemmas and nine resolution-existence theorems prove `IsTransverse` for the smooth strict transform and the accumulated SNC boundary, retaining the original resolution conclusions. Direct existence forms include compact pure/mixed-dimensional sets, compact ambient pure forms, pure relatively compact restrictions, and the boundary neighbourhood form. Other original forms can use the generic upgrades. |
| `Hironaka.HironakaDivisorPowers` | Ten theorems prove multiplicity scaling for actual ideal powers, including restricted submanifolds and the zeroth power, and produce nonzero stalks from actual invertibility. |
| `Hironaka.HironakaDivisorResidual` | Seven theorems and a recursive finite-product definition produce constant multiplicities on connected smooth carriers and actual residual factorizations for a finite ordered list of nonempty connected smooth closed hypersurfaces. The residual support shrinks and contains none of the chosen hypersurfaces entirely. |

The continuation modules prove the complete SNC divisor-sum dictionary. Genuine connected components are constructed from disconnected boundary members; their multiplicities are the original divisor's exponents. Compact support gives an actual finite component sum, while arbitrary noncompact support gives one global coefficient function and locally finite positive component sums whose complete ideal stalks agree with the divisor on every selected open neighbourhood. The residual unit and coefficient identities are produced internally. Canonical compact-support principalization retains the original conclusions and this actual sum.

The current centre modules internally produce the original reduced invertible ideal of a pure hypersurface, identify every controlled strict ideal, terminate arbitrary multiplicity restarts and retain literal centre conditions at every stage, then append smooth boundary resolution. Actual curve-cosupport data produce an unconditional global canonical growing sequence, locally finite centre images and compact-uniform eventual geometric resolution. Actual order tuples, boundary counts, monomial and special StepOne strata have analytic superlevels. General NC charts produce original local branches and fixed-sequence permutation compatibility. Actual blowups of the same centre produce comparison cocycles. Full higher-dimensional global resolution and unordered canonical boundary descent remain open.

The third continuation identifies intrinsic whole-ideal embedding dimension, complete dimension-two StepOne analytic superlevels, unique NC branch overlaps and smooth highest strata with internally attained maxima. Genuine holomorphic jets identify the actual maximal-ideal powers with derivative kernels and prove finite dimension of R/(I+m^q) for any original ideal. Actual finite curve-history predicates internally produce a global zero-dimensional exception. Original holomorphic submersion charts internally produce a section through the point and preserve entire ideal order and cosupport across different dimensions. Higher-invariant smooth functoriality, normal-flat centres and general Hilbert–Samuel transformation descent remain open.

The fourth continuation checkpoint adds whole coherent colon and controlled-transform extension, actual finite monomial and whole-ideal Macaulay spans, derivative-ideal pullback inclusion for arbitrary holomorphic maps, genuine GeneralTwo companion curve loci, and real highest-stratum blowups preserving the original NC carrier jointly with the accumulated SNC boundary. Nine additive modules preserve every earlier mathematical source file. Their original declaration types, definition values and theorem proof terms are checked exactly under the canonical namespace rename; see [the fourth verification report](audit/continuation-20261011-r1-batch4/verification.md).

The fifth continuation checkpoint proves genuine finite holomorphic Macaulay minor equations for whole coherent chart stalks, chart independence of the intrinsic Hilbert–Samuel function and all its global analytic superlevels, every literal GeneralTwo canonical analytic superlevel, and actual finite NC separation in at most n-1 steps with a smooth transverse differential strict carrier and an isomorphism on the original carrier complement. All eight new modules pass exact declaration and proof-term comparison and independent kernel replay; see [the fifth verification report](audit/continuation-20261011-r1-batch5/verification.md). Higher-dimensional global recursion, general smooth functoriality and full Hilbert–Samuel descent remain open.

The complete statements and mathematical proofs are in [the extension blueprint](blueprint/extensions.tex). Reusable support modules supply original geometric and ideal-theoretic declarations omitted by the first release's extraction.

## Local sharp curve endpoints and controlled smooth pullback (15 October 2026)

`Hironaka.HironakaSharpActualCurveLocalSharpEndpoints.exists_original_curve_actual_local_sharp_endpoint` starts from an original smooth curve, its indexed SNC boundary and density off that boundary, and any base point. It constructs an actual open neighbourhood and a finite genuine TEST history whose endpoint is transverse to the entire accumulated ordered boundary. The same composite projection is an isomorphism over the whole original local normal-crossings good locus. Compactness of the local cosupport is proved internally using an actual isolating neighbourhood; no compact-window or completed-history certificate is required. The subsequent overlap-map results below compare these local histories; constructing their global geometric descent and a general noncompact global sharp history remains open.

`Hironaka.HironakaOriginalUntestedControlledSmoothPullback` proves equality of the entire controlled marked records under genuine smooth pullback, including the original reference history and every literal prefix. It preserves actual coherent numerators and smooth strict carriers, and derives the needed reference geometry from original two-dimensional DOMAIN data, a nonempty actual member and an arbitrary upper TEST. This controlled-record theorem retains the complete reference history; lower current-cosupport membership and whole value comparisons are separate statements.

Both completed subgoals and their full dependency closures are synchronized from accepted source checkpoints. The complete blueprint chapters and reproducible source provenance are in [the curve endpoint audit](audit/local-sharp-curves-20261015/verification.md) and [the controlled pullback audit](audit/controlled-smooth-pullback-20261015/verification.md).

## Reduced formal standard bases and actual stage comparison (15 October 2026)

[`HironakaActualReducedFormalStandardBasis`](Hironaka/Resolution/HironakaActualReducedFormalStandardBasis.lean) constructs the unique canonical normal representative of every formal ideal class and the reduced vertex members `Gₐ = Xᵃ − Rᵢ(Xᵃ)`. These actual reduced members generate the entire original formal ideal. Existence, uniqueness and generation are proved internally; general permissible-centre compatibility, transformed presentations and Bennett inequalities remain open.

[`HironakaOriginalControlledReferenceRestriction`](Hironaka/Resolution/HironakaOriginalControlledReferenceRestriction.lean) derives the genuine one-sided controlled inclusion on an actual smaller strict carrier from the full reference data. [`HironakaSharpActualCurveDefectRestriction`](Hironaka/Resolution/HironakaSharpActualCurveDefectRestriction.lean) proves restriction of the actual curve defects; [`HironakaSharpActualCurveStageComparison`](Hironaka/Resolution/HironakaSharpActualCurveStageComparison.lean) identifies the actual first centres and uniquely compares the next genuine blowups. The subsequent common-open comparison and cocycle results below advance overlap gluing; full geometric descent remains open.

The four subgoals and their 49-module dependency closure retain 49 complete blueprint chapters with 209 original proofs. Three additional support modules recover five complete original declarations. Every one of the **1,656 actual new compiled declarations**, including all **1,386 theorem proofs**, passes complete structural type and value comparison. The [verification report](audit/reduced-basis-curve-comparison-20261015/verification.md) records source provenance, declaration-scoped original instance contexts and the five precisely witnessed imported-binder owner relocations.

## Reduced division, smooth value cases and retained curve recipes (15 October 2026)

[`HironakaActualReducedBasisDivision`](Hironaka/Resolution/HironakaActualReducedBasisDivision.lean) proves whole formal division by the actual canonical reduced vertex members, including the quotient centre-power bounds. [`HironakaActualCoefficientPresentationCentrePower`](Hironaka/Resolution/HironakaActualCoefficientPresentationCentrePower.lean) derives whole formal centre powers from genuine coherent coefficient cosupport and literal Taylor coefficient identities. Construction of arbitrary local coefficient presentations, their transformed stability and Bennett inequalities remain open.

The smooth-pullback results now include original controlled lower current-cosupport membership, actual special and companion values, whole general values for target curve data in any source relative dimension, positive StepOne values in any relative dimension, and all StepOne branches in equal dimension. General higher-dimensional whole-value and history compatibility remains open.

The curve results now retain actual local first blowups and terminating recipes, restrict the literal recipes to smaller opens, construct genuine empty-blowup padding and uniquely compare unequal terminal histories. These are completed subgoals. The following checkpoint supplies actual comparisons between different neighbourhoods on common opens and a finite-recipe cocycle; global geometric descent remains open.

The 13 synchronized subgoals add 21 complete modules and one pure support module. All **452 actual added declarations**, including **342 complete theorem proofs**, match their original complete types and values. Their 21 complete blueprint chapters retain all 83 original proofs; see [the verification report](audit/retained-recipes-and-reduced-division-20261015/verification.md).

## Local coefficient generators and genuine curve overlap maps (15 October 2026)

[`HironakaActualLocalCoefficientStrictGenerators`](Hironaka/Resolution/HironakaActualLocalCoefficientStrictGenerators.lean) starts from an actual coherent coefficient presentation on one genuine open neighbourhood and its local centre cosupport. It internally derives the canonical reduced members' exact centre orders and finite generators of the **entire genuine formal strict-transform ideal**. No global extension of the coefficient ideals is assumed. Constructing the full general coefficient presentation, proving its transformed stability, and the analytic strict-transform bridge and Bennett inequalities remain open.

The original smooth-pullback results now construct genuine Cartesian source choices, derive candidate DOMAIN data on the same carrier, and prove the zero own SMALL and LARGE whole-value cases in arbitrary relative dimension. [`HironakaOriginalRunCompanionSpecialSmooth`](Hironaka/Resolution/HironakaOriginalRunCompanionSpecialSmooth.lean) proves the actual run-companion special-value and level dictionaries. General higher-invariant values and arbitrary-history compatibility remain open.

[`HironakaSharpActualCurveOverlapMaps`](Hironaka/Resolution/HironakaSharpActualCurveOverlapMaps.lean) constructs actual comparison maps between independently chosen finite curve recipes on genuine common opens. It supplies the true first-centre and boundary dictionaries before applying blowup comparison. [`HironakaSharpActualCurveCommonOpenCocycle`](Hironaka/Resolution/HironakaSharpActualCurveCommonOpenCocycle.lean) proves a triple cocycle for finite recipes on the same common open, using genuine identity empty-tail padding and uniqueness. Restriction compatibility for already chosen pairwise-intersection maps and their global geometric descent are subsequent goals.

The 11 synchronized subgoals and their dependency closure add 67 whole modules and three pure original support modules. All **1,088 actual added declarations**, including **877 complete theorem proofs**, match the original complete types and values. Their 67 complete blueprint chapters retain all 240 original proofs; see [the verification report](audit/local-coefficients-and-curve-overlaps-20261015/verification.md).

## Latest completed subgoals

* **Actual completion, analytic relations and blowup quotients:** [`HironakaActualOriginalAdicCompletion`](Hironaka/Resolution/HironakaActualOriginalAdicCompletion.lean) identifies the genuine maximal-adic completion of the original holomorphic germ ring with the formal power-series ring, compatibly with the original Taylor map. [`HironakaActualTaylorFaithfullyFlat`](Hironaka/Resolution/HironakaActualTaylorFaithfullyFlat.lean) proves this map faithfully flat and produces finite original analytic syzygies for every formal relation on a finite analytic family; [whole ideal intersections](Hironaka/Resolution/HironakaActualFormalIdealIntersections.lean) commute with Taylor extension. Actual analytic normal powers contract exactly from their formal counterparts. [Finite local coefficient ideals](Hironaka/Resolution/HironakaActualFiniteCoefficientIdeals.lean) and [analytic exceptional quotients](Hironaka/Resolution/HironakaActualCoefficientAnalyticBlowup.lean) are constructed on genuine common holomorphic domains under the stated coefficient-cosupport conditions. General permissible-centre presentations, their transformed stability and Bennett inequalities remain open.
* **The same given smooth history and actual prepared values:** the [given-history StepOne comparison](Hironaka/Resolution/HironakaOriginalGivenSmoothStepOneValues.lean) retains an arbitrary given genuine Cartesian upper history. The [prepared full GENERAL comparison](Hironaka/Resolution/HironakaOriginalPreparedGeneralSmoothValues.lean) treats original carrier bound two, a depth-two canonical prefix and one actual admissible preparation step, without assuming that next step canonical. It internally supplies the actual companion tests and current lower points and compares full values at every stated depth `d+2` on the same source history. The complete higher-dimensional canonical endpoint, arbitrary-history compatibility and terminating global scheduler remain open.
* **A proper global endpoint for original smooth curves:** the [original recipe atlas](Hironaka/Resolution/HironakaSharpActualCurveOriginalRecipeAtlas.lean) constructs the covering local recipes and their comparisons from the original closed smooth pure curve, ordered SNC boundary and density off that boundary. The [global manifold](Hironaka/Resolution/HironakaSharpActualCurveGlobalManifold.lean) is Hausdorff and second countable, with a genuine proper holomorphic projection. The actual glued curve is globally smooth of dimension one, its [locally finite indexed boundary has SNC and transverse coordinates](Hironaka/Resolution/HironakaSharpActualCurveGlobalBoundaryCoordinates.lean), and the same projection is an [isomorphism over the entire original good locus](Hironaka/Resolution/HironakaSharpActualCurveGlobalGoodIsomorphism.lean). The conventional global strict-closure identity and an actual global blowup schedule remain separate goals; no higher-dimensional sharp driver is claimed.

This public snapshot reproduces the accepted native **313-module** continuation checkpoint, published in [upstream PR111](https://github.com/MingchenXia/archon-nakamaye/pull/111) at the [fixed source revision](https://github.com/MingchenXia/archon-nakamaye/commit/7266ce19c9d3f79a8693f7ded964755af7af59a7). The increment beyond the preceding 280-module checkpoint contains 33 whole original modules, one pure support module with three complete original proofs, and 33 complete blueprint chapters with 76 proofs. Every one of its **292 actual added declarations**, including **241 complete theorem proofs**, matches the original complete type and value. Later native checkpoints are separate progress and are not counted in this snapshot's verified totals.

## Status of the nine original gaps

G5–G7 are **closed**, as recorded in the table above. They are no longer missing features. The six remaining gaps and their completed cases are:

| Gap | Completed part | Remaining part |
|---|---|---|
| G1 | Embedded resolution and principalization in complex manifolds. | Abstract analytic spaces and characteristic-zero algebraic categories. |
| G2 | Canonical principalization for compact zero locus and actual divisor sums; original DOMAIN2 StepOne comparisons on the same given Cartesian histories; full GENERAL comparisons after one admissible preparation step at the stated positive depths, with internally constructed current lower tests and points. | The complete general canonical elementary endpoint, higher-carrier-bound and arbitrary-history compatibility, and terminating global scheduling. |
| G3 | A global canonical growing sequence with locally finite centre images and compact-uniform stabilization for initial cosupport of dimension at most one; terminal-map and comparison constructions. | The actual globally scheduled locally finite blowup history and terminal-space identification in general dimension. |
| G4 | An actual proper global complex endpoint from original smooth-curve data, with a global smooth glued curve, locally finite indexed SNC boundary transverse to it, and isomorphism over the entire original good locus. | Conventional global strict-closure identification and an actual global blowup history; the complete higher-dimensional defect invariant, decrease and termination. |
| G8 | Compact hypersurface stage control; canonical reduced formal bases and division; actual relative coefficient germs; the genuine analytic adic completion and faithfully flat Taylor map, original analytic syzygies and whole ideal intersections; actual analytic centre powers and exceptional quotients from finite coherent coefficient data. | General permissible-centre compatibility and the complete analytic/formal strict-transform bridge, transformed presentations, stability and Bennett inequalities. |
| G9 | Genuine local NC branches and whole divisor stalks; permutation and indexed-SNC procedure comparisons. | Global canonical descent for local branches and self-intersections, alignment with the main driver and additional ideals. |

The following descriptions record the precise scope of each original item; **items 5–7 describe completed results**, while the other items distinguish proved cases from outstanding generalizations.

1. **Scope.** The ambient space is always a complex manifold (smooth); singular analytic spaces appear only as analytic
   subsets of a manifold (embedded resolution) or through ideal sheaves (principalization). There is no statement about
   abstract analytic spaces, algebraic varieties, schemes, or fields other than `ℂ`.
2. **Canonical elementary principalization is proved for compact zero locus.** The continuation theorem
   `Hironaka.HironakaCompleteDivisorSum.exists_canonical_principalization_componentSum` constructs the actual
   canonical tower on an arbitrary ambient manifold with compact ideal zero locus, retaining open restriction,
   biholomorphism uniqueness and all principalization conclusions. General smooth-morphism functoriality and
   fully canonical elementary embedded resolution remain open.
3. **Compactness.** A finite blowup sequence is produced when `X` is compact, or when `Z(𝔞)` (resp. `V`, `W`) is
   compact; otherwise the original API provides relatively compact restrictions. The continuation now produces
   a genuine global canonical sequence with locally finite centre images and compact-uniform stabilization
   when the actual initial cosupport has geometric dimension at most one. General higher-dimensional
   global sequence existence and its terminal analytic space remain open.
4. **Sharp embedded resolution is proved locally for original smooth curves; the general form remains open.**
   The new local curve theorem above preserves the whole original NC good locus and makes the entire ordered boundary
   transverse. The original `*_boundary*` API theorems still permit centres over
   `F = W_sing ∪ (W ∩ |E₀|)`. General higher-dimensional sharp centres, the complete defect invariant and termination,
   and the remaining conventional strict-transform and global-history identifications for the constructed smooth-curve endpoint remain open.
5. **Dimension components: identification proved.** The extension theorem
   `Hironaka.HironakaDimensionGlobalComponents.dimensionPart_eq_sUnion_globalComponents` identifies
   `W⁽ᵏ⁾ = closure (Reg_k W)` with the union of the genuine global irreducible components of pure geometric
   dimension `k`, for every analytic `W` and every `k`. Its finite local decomposition retains exactly the branches
   of dimension `k`. Existing mixed-dimensional resolution results still have the compactness or local restrictions
   in item 3 and assume `interior W = ∅`.
6. **Complete SNC divisor sums are proved.** `Hironaka.HironakaCompleteDivisorSum` gives actual finite sums
   for compact support and the same actual canonical principalization tower. `Hironaka.HironakaLocallyFiniteDivisorSum`
   gives arbitrary noncompact locally finite sums with one global original-coefficient function and full local ideal
   equality. Disconnected SNC members, zero coefficients, empty boundaries and ambient dimension zero are covered.
7. **Simultaneous normal crossings: noncontainment proved in the extension.** The original predicate
   `HasNormalCrossings S E` permits a boundary member to contain `S` locally. The extension derives `IsTransverse S E`
   from actual normal-crossings coordinates and density off the boundary, and proves it for strict transforms using
   admissibility and the original exceptional-support conclusions. Nine directly named existence forms retain all
   original conclusions and append transversality; four generic lemmas also upgrade the other original forms.
   The original 42 API declarations themselves retain their previous statements.
8. **Full compact hypersurface stage control is proved.** The original reduced ideal is internally invertible;
   every controlled strict ideal is identified with the actual reduced current strict ideal. Unbounded multiplicity
   restarts terminate, and every centre obeys literal current-transform singular or smooth-boundary conditions.
   Higher codimension, full Hilbert–Samuel descent and normal-flat centres remain open.
9. **General normal crossings remains open.** Genuine initial NC charts now produce the complete original
   local divisor stalk and SNC local branches, with fixed-sequence permutation compatibility. Global unordered
   canonical descent with the required cosupport and isomorphism conditions remains open; the existing
   resolution API still assumes an initial SNC list.

## Building

You need [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.33.1`) and Mathlib is pinned to commit `0df444a360eaa60ab8c11dca51a86af692955474` (tag `v4.33.1`) in `lakefile.toml` and `lake-manifest.json`.

```sh
export LEAN_NUM_THREADS=2 # match the validated build and CI thread budget
lake exe cache get      # download the compiled Mathlib
lake build --wfail      # build the library; fail on warnings
lake test               # print and check the axioms (scripts/CheckAxioms.lean)
lake env lean scripts/CheckExtensions.lean # original extension audit
lake env lean scripts/CheckContinuations.lean # audit continuation and support constants
lake env lean audit/local-sharp-curves-20261015/CheckAllCompiledRoots.lean # all actual local roots
lake env leanchecker Hironaka   # optional: replay every module in the kernel
```

To use the library from another Lake project on the same Mathlib:

```toml
[[require]]
name = "Hironaka"
git = "<URL of this repository>"
rev = "main"
```

## Axioms

Every declaration of the library, and in particular every public theorem, depends only on the three standard axioms of Lean and Mathlib: `propext`, `Classical.choice` and `Quot.sound`. The library declares no axioms of its own. `scripts/CheckAxioms.lean` checks the public namespace; the complete compiled-module audit in `audit/analytic-completion-and-global-curve-atlas-20261018/CheckAllActualCompiledRoots.lean` also covers private, generated and globally named helper declarations.

The sixth continuation checkpoint adds actual dimension-three companion lower patches and nonspecial current-level GeneralThree analytic thresholds, intrinsic first Hilbert–Samuel tangent values and their exact pure-dimensional singular-locus dictionary, and actual biholomorphic preservation of unordered NC multiplicities. All 484 earlier mathematical modules remain byte identical; 60 types/definitions and 42 theorem proof terms compare exactly, all 89 actual new constants pass the axiom allowlist, and all four new modules pass independent kernel replay. The general gaps listed above remain open.

The seventh continuation checkpoint adds genuine submersion Jacobian pivots, arbitrary-choice NC separating-tower comparisons and cocycles, actual three-dimensional canonical curve envelopes and history exceptions, and frames of entire jet stalk quotients on internally produced constant-rank patches. All 488 previous mathematical modules remain byte identical. All 142 types/definitions and 91 theorem proof terms compare exactly, all 243 actual new constants pass the allowlist, and all five new modules pass kernel replay. The broader general gaps remain open.

The eighth continuation checkpoint adds entire iterated-derivative ideal equality under genuine smooth submersions, whole relative normal-coordinate power quotients and internally finite relative modules, actual dimension-three member lower tails, and empty-centre compression for real NC towers under open restrictions. All 493 earlier mathematical modules remain byte identical. All 107 types/definitions and 79 theorem proof terms compare exactly, all 153 actual new constants pass the allowlist, and all seven new modules pass kernel replay. Existing pure support is reused; three missing fragments are extracted exactly. The general gaps listed above remain open.

The ninth continuation checkpoint adds whole original coefficient marked data under genuine smooth pullback, original smooth-centre ideal/power quotient dictionaries, complete dimension-three member lower tails, and entire original NC total ideals on augmented terminal boundaries. All 500 earlier mathematical modules remain byte identical. All 87 declaration types/definitions and 68 theorem proof terms compare exactly, and all seven new modules pass kernel replay. Existing pure support is reused; three missing fragments are extracted exactly. The six general gaps remain open.

The tenth continuation checkpoint adds complete whole relative Taylor coefficient kernels and entire original ideal quotients, actual marking-one admissibility and residual unit on the augmented NC terminal boundary, real member lower order histories, and entire original homogenized marked records under genuine smooth pullback. All 507 earlier mathematical modules remain byte identical. All 93 declaration types/definitions and 78 theorem proof terms compare exactly. Four missing pure support fragments are copied exactly, with existing support reused. The six general gaps remain open.

The eleventh continuation checkpoint adds actual whole ambient normal monomial bases in every degree, entire original member companion controlled histories, and genuine component-own positive special/count history exceptions. All 515 preceding mathematical modules remain byte identical. All 75 declaration types/definitions and 53 theorem proof terms compare exactly. The six general goals remain open.

The twelfth continuation checkpoint adds actual whole relative normal ideal matrices and fixed-degree localized quotient freeness, exact original divisor exponents under smooth submersions, and whole original NC total/controlled indexed exponent dictionaries. All 518 earlier mathematical modules remain byte identical. The three complete modules and five previously missing pure exact support fragments have all 105 declaration types/definitions and 94 theorem proof terms identical under canonical renaming, with zero fallback. All-degree analytic normal-flat spreading and the six general goals remain open.

The thirteenth continuation checkpoint adds the complete original relative associated graded quotient and monomial-symbol dictionary, actual positive first-entry values across every original member-companion mask, and entire genuine smooth pullback of invertible quotients and original residual marked records. All 526 earlier mathematical modules remain byte identical. All 62 declaration types/definitions and 47 theorem proof terms compare exactly, with zero fallback; existing pure support is reused without new fragments. All six general gaps remain open.

The fourteenth continuation checkpoint adds genuine whole original standard normal monomial bases and one actual uniform denominator, actual masked monomial values and complete finite marked SNC procedures. All 529 earlier mathematical modules remain byte identical. All 123 declaration types/definitions and 93 theorem proof terms compare exactly, with zero fallback; four missing pure support fragments preserve their original complete declaration contexts. All six general gaps remain open.

The fifteenth continuation checkpoint adds actual monomial ordering under genuine smooth pullback, source member-head incidence, complete ordered monomial tails and original values across every member mask. All 537 preceding mathematical modules remain byte identical. All 125 actual new compiled constants and 111 theorem proof bodies compare fully and exactly, including every private/compiler helper, with zero fallback, alpha/defeq comparison or numerical erasure. The complete 9696-constant library audit and explicit kernel replay of all eight new modules pass. G1, G2, G3, G4, G8 and G9 remain open.

## Verification

The current [verification report](audit/analytic-completion-and-global-curve-atlas-20261018/verification.md) and [machine-readable receipt](audit/analytic-completion-and-global-curve-atlas-20261018/final-validation.json) cover this increment:

* **Build and axioms:** `lake --wfail build` passed all 4,994 jobs with zero warnings. All 16,863 actual library roots use only `propext`, `Classical.choice` and `Quot.sound`. All 5,408 distinct local declaration bindings in the full blueprint resolve in the compiled library.
* **Complete expression comparison:** all **292 added actual roots** match their original complete types and values, including all **241 complete theorem proofs** and every private/generated helper. Numerical name components, binder names and metadata are retained. The frozen AllV2 and ScopedOwnersV3 profiles and comparator use no alpha-equivalence, definitional-equivalence or erasure fallback. Lossless compressed captures reproduce the full comparison.
* **Kernel coverage:** all 34 new modules and the changed import root passed fresh frozen replay. All 968 preceding mathematical sources and complete kernel-data artifacts match the pinned preceding verified checkpoint byte for byte. This chain covers all 1,003 modules; it does not claim a fresh full-library replay.
* **Source provenance:** the 33 whole modules and 33 complete blueprint chapters reproduce from the [fixed normal published source](https://github.com/MingchenXia/archon-nakamaye/commit/7266ce19c9d3f79a8693f7ded964755af7af59a7). One additive pure support module recovers three complete original admissibility proofs with their entire original Generic and Masked contexts. Two declaration-local instance restorations select the exact original compiled instance paths without changing declaration or proof text. Independent source/context reviews and complete expression comparison verify these restorations. None of the preceding 968 mathematical sources changes.
* **Blueprint scope:** 390 complete synchronized chapters contain 1,541 complete proofs, with 4,249 distinct local bindings, 241 verified upstream-only bindings and two explicitly unresolved historical attachment names. The full document includes 475 chapters, 2,012 proof environments and 5,408 distinct local bindings. Its [786-page PDF](audit/analytic-completion-and-global-curve-atlas-20261018/blueprint-pdf-build/extensions.pdf) compiles without LaTeX errors. Preserved external-reference and bookmark warnings are recorded in the receipt.
* **Previously disclosed parser outputs:** the preceding checkpoint separately audited three generated front-end definitions of a local notation. Their relocated generated names and quoted hygiene identifiers differ, so that checkpoint's raw all-1,009-root comparison remains explicitly `BLOCKED_EXACT_DIFFERENCE`; equality of those three bodies remains unclaimed. Their source-generation evidence and full axiom/kernel coverage remain included through the verified preceding checkpoint. This increment has no such unmatched new roots.

Reproduce source recovery and compare the complete recorded expressions with:

```sh
python3 audit/analytic-completion-and-global-curve-atlas-20261018/verify_incremental_source.py --source-root /path/to/archon-nakamaye
python3 audit/analytic-completion-and-global-curve-atlas-20261018/verify_recorded_full_expressions.py
```

Source build, actual-root axiom audit, captured-data comparison and frozen kernel replay are separate checks. The [preceding verification](audit/analytic-coefficient-dictionary-and-chosen-overlaps-20261015/verification.md) retains its original complete evidence and explicit parser disclosures. G5, G6 and G7 remain closed; G1, G2, G3, G4, G8 and G9 retain the outstanding general goals listed above.

<details>
<summary>Historical verification of the original v0.1 release</summary>

The following evidence describes the original v0.1 release (352 modules, 3557 declarations, 94679 lines of Lean). Verification of the original extensions is recorded separately in [their audit report](audit/extensions-20261011/verification.md), and the current continuations in [the first report](audit/continuation-20261011-r1/verification.md), [the second report](audit/continuation-20261011-r1-batch2/verification.md) and [the third report](audit/continuation-20261011-r1-batch3/verification.md):

* **Build**: `lake build` from scratch: exit code 0, 352 modules compiled, 0 errors, 0 warnings, 0 declarations with an incomplete proof, 2470 s with one Lean process at a time.
* **Axioms**: `#print axioms` on each of the 42 public theorems and `collectAxioms` on all 4439 declarations: every public theorem depends exactly on `Classical.choice`, `Quot.sound`, `propext`; all 4439 declarations depend on these three at most.
* **Faithfulness**: every declaration of the library was compared with the declaration it was extracted from, in one Lean environment containing both (types, definition bodies and inductive types, up to the renaming of names): 42/42 public theorem statements equal; of the 4438 compared declarations, 4435 are syntactically equal and 3 equal up to definitional unfolding (all of them differ only in the numbering of `_proof_N` auxiliary lemmas), 0 differ; the 24 further declarations of the library (generated or auxiliary) all have an equal original (0 exceptions); 3522/3531 proof terms identical.
* **Kernel replay**: `leanchecker` on all 352 modules: exit code 0, 352 modules replayed, 0 problems.
* **Source scan**: 359 files scanned for e-mail addresses, incomplete-proof markers, declarations of axioms, kernel-bypassing tactics, internal identifiers and internal paths: 0 hits.

</details>

## Layout

| directory | contents |
|---|---|
| `Hironaka/Manifold` | complex manifolds, holomorphic maps, local inverses |
| `Hironaka/Analytic` | analytic subsets, germ rings, Weierstrass preparation, Noether normalization, parametrization, dimension, ideal sheaves |
| `Hironaka/Coherence` | Oka's coherence theorem and Cartan's coherence of the ideal sheaf of an analytic subset |
| `Hironaka/Blowup` | the blowup along a smooth centre (construction, universal property), towers of blowups, exceptional divisors, normal crossings |
| `Hironaka/MarkedIdeal` | marked ideals, orders, derivative and coefficient ideals, homogenization, maximal contact, Giraud's lemma |
| `Hironaka/Invariant` | the resolution invariant: Step 1 (maximal order), the general step, the monomial case, canonical centres |
| `Hironaka/Resolution` | the canonical resolution, principalization, embedded resolution and their variants |
| `Hironaka/API.lean, Hironaka/API2.lean, Hironaka/API3.lean, Hironaka/API4.lean` | the public statements |

Namespaces follow the module structure of the development the library was extracted from: the declarations of the module `Hironaka/<Area>/<Name>.lean` are in the namespace `Hironaka.<Name>` (except the public statements, which are in `Hironaka`). The module `Hironaka/Invariant/StepOneSeq.lean` generates part of its declarations with the command `transport_ext_to_seq` of `Hironaka/Invariant/ExtSeqTransport.lean`, which re-states results proved for one form of the resolution invariant for another and adds each one through the kernel.

Some docstrings refer to statements of the LaTeX write-up from which the formalization was developed by labels such as `hir:general-step`; the full original write-up is not part of this repository. The new extension chapters are included under `blueprint/`. Labels such as `pr:resol` or `le:S` are those of the arXiv source of Włodarczyk 2005, and keys such as `wlodarczyk05-hironaka` refer to the references below.

## References

* `hironaka64`: H. Hironaka, *Resolution of singularities of an algebraic variety over a field of characteristic zero I, II*, Ann. of Math. (2) 79 (1964), 109--203 and 205--326.
* `bierstone-milman97-invent-math`: E. Bierstone, P. D. Milman, *Canonical desingularization in characteristic zero by blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207--302.
* `bierstone-milman03-desingularization-algorithms`: E. Bierstone, P. D. Milman, *Desingularization algorithms I. Role of exceptional divisors*, Mosc. Math. J. 3 (2003), 751--805.
* `bierstone-milman08-functoriality`: E. Bierstone, P. D. Milman, *Functoriality in resolution of singularities*, Publ. Res. Inst. Math. Sci. 44 (2008), 609--639.
* `encinas-hauser02-strong-resolution`: S. Encinas, H. Hauser, *Strong resolution of singularities in characteristic zero*, Comment. Math. Helv. 77 (2002), 821--845.
* `hauser03-hironaka-theorem`: H. Hauser, *The Hironaka theorem on resolution of singularities (or: A proof we always wanted to understand)*, Bull. Amer. Math. Soc. 40 (2003), 323--403.
* `kollar07-resolution`: J. Kollár, *Lectures on resolution of singularities*, Annals of Mathematics Studies 166, Princeton University Press, 2007 (arXiv:math/0508332).
* `wlodarczyk05-hironaka`: J. Włodarczyk, *Simple Hironaka resolution in characteristic zero*, J. Amer. Math. Soc. 18 (2005), 779--822.
* `wlodarczyk09-analytic-resolution`: J. Włodarczyk, *Resolution of singularities of analytic spaces*, Proceedings of the Gökova Geometry-Topology Conference 2008 (2009), 31--63.
* `cartan50`: H. Cartan, *Idéaux et modules de fonctions analytiques de variables complexes*, Bull. Soc. Math. France 78 (1950), 29--64.
* `oka50`: K. Oka, *Sur quelques notions arithmétiques*, Bull. Soc. Math. France 78 (1950), 1--27.
* `griffiths-harris`: P. Griffiths, J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978.

## Authors and license

The original release was written by AI agents (Claude, by Anthropic). Later continuation and synchronization files credit Hironaka contributors in their headers. The library is released under the Apache License 2.0 (see `LICENSE`).
