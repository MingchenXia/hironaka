# Public API

## Geometric setting

The original public API statements are about complex manifolds of dimension `n`, given unbundled:

```lean
{X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
```

where `ComplexModel n = EuclideanSpace ℂ (Fin n)` and `IsComplexManifold n X` asks for a Hausdorff, second countable topological space with a holomorphic atlas (Mathlib's `IsManifold 𝓘(ℂ, ℂⁿ) ∞`). These original API statements are complex-analytic. The original global finite-sequence existence theorems assume **compactness**: either `X` is compact, or the relevant set (`Z(𝔞)`, `V`, `W`) is compact; otherwise the results hold over open sets contained in a compact set, or over a **relatively compact** neighbourhood of any compact set.

Vocabulary (all in this library): `GermIdeal n X` is an ideal sheaf of holomorphic germs, with `IsCoherent`, `zeroLocus` (`Z(𝔞)`), `pullback`; `EffectiveDivisor` is an invertible ideal sheaf `𝒪(-D)` with its support; `ClosedIrreducibleAnalyticSubvariety` and `IsComplexAnalyticSubset` are analytic subsets; `Hironaka.singularLocus V = V \ V_reg` (`V_sing`), and `W_sing = W \ regularLocus W d`; `IsSNCDivisor n E` says that the closed members of the list `E` have simple normal crossings (at every point the members through it are distinct coordinate hyperplanes of one chart); an *admissible blowup sequence* of `(X, E₀)` over `F` (`HironakaAdmissibleSequence.IsAdmissibleBlowupSequence n X E₀ F X' f E`) is a finite composition `f : X' → X` of blowups with smooth centres, each centre having only normal crossings with the divisor accumulated so far and lying over `F`; `E` starts with the strict transforms of the members of `E₀`, then has one member per blowup. `exceptionalLocus` (`Exc f`), `strictTransform` and `IsIsomorphismOver` have their usual meaning.

## De Jong alterations over arbitrary fields

`Hironaka.DeJong` is a separate scheme-theoretic API, also exported by
`import Hironaka`. Its field has no characteristic, perfectness or
algebraic-closedness restriction. The input variety is integral, separated and
of finite type; it need not be geometrically integral.

| theorem | statement |
|---|---|
| `Hironaka.deJongAlterationTheorem` | For every field `k`, the unchanged native proposition `DeJongAlterations.DeJongAlterationTheorem k`. Its only inputs are `(k : Type u) [Field k]`. |
| `Hironaka.exists_alterationWithBoundary` | For an actual `k`-variety `X` and any prescribed proper closed subset `Z`, a genuine alteration `Y → X`, an open immersion `j : Y → Ybar`, an integral regular projective `k`-variety `Ybar`, and a strict SNC boundary whose support is exactly `j(f⁻¹(Z)) ∪ (Ybar \ j(Y))`. |

The boundary includes the effective Cartier, reducedness, regular-intersection
and pure-codimension conditions of the native strict SNC definition. This API
does not assert that the alteration is birational, nor add the separate
perfect-field generically-étale refinement. Over an imperfect field,
regularity of the compactification is the stated conclusion.
See [the detailed API, fixed source and verification](DEJONG.md).

## Original complex-analytic API

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

## Invariant, controlled-ideal and gluing prerequisites

The following modules are available through `import Hironaka`. Their original
theorem namespaces and hypotheses are preserved; they do not assert the remaining
general canonical stabilization or noncompact resolution theorem.

| Module suffix in `Hironaka.Resolution` | Proved scope |
|---|---|
| `HironakaDisjointZeroCoordinateInitialRecoding`, `HironakaDisjointCoherentNormalRecoding` | The exact initial invariant depth shift and first canonical maximum locus under normal stabilization, including arbitrary coherent nonradical ideals. |
| `HironakaDisjointControlledNormalPivot`, `HironakaDisjointFlattenedNormalKernel` | Actual current normal-pivot exclusion and whole local normal-kernel containment. |
| `HironakaDisjointMatchedControlledTrace`, `HironakaDisjointActualControlledSplit`, `HironakaDisjointActualGlobalControlledSplit` | Matched actual ambient/native blowup charts and whole controlled-ideal trace and reconstruction at every current cosupport point. |
| `HironakaDisjointCompactExhaustionEscape` | Local finiteness of actual centres is equivalent to compact-exhaustion escape, with corresponding protected opens; an escaping sequence is not supplied. |
| `HironakaDisjointAnalyticSaturatedGluing`, `HironakaDisjointProperAnalyticGluing` | Actual analytic gluing over saturated windows, including Hausdorffness and second countability, and a global proper analytic map from compatible local proper maps. |
| `HironakaDisjointInvariantOrdinal` | Exact ordinal encoding of the full recursive value type and chronological boundary labels; geometric descent and termination remain separate. |

The [scope and verification record](../STATUS.md#verification-and-source) gives
the fixed native source and complete source, blueprint and expression audits.
