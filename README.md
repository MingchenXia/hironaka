# Hironaka

A Lean 4 / Mathlib formalization of **resolution of singularities in complex-analytic geometry**: principalization of coherent ideal sheaves and embedded resolution of analytic subsets of complex manifolds, by finite sequences of blowups with smooth centres, together with the canonical resolution of marked ideals from which both are derived (in the style of Włodarczyk and Bierstone--Milman).

The library was produced by AI agents (Claude) formalizing mathematics in Lean 4; every file has `Authors: Claude`. It is checked by Lean's kernel; see [Verification](#verification).

## Setting

All statements are about complex manifolds of dimension `n`, given unbundled:

```lean
{X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
```

where `ComplexModel n = EuclideanSpace ℂ (Fin n)` and `IsComplexManifold n X` asks for a Hausdorff, second countable topological space with a holomorphic atlas (Mathlib's `IsManifold 𝓘(ℂ, ℂⁿ) ∞`). Everything is complex-analytic. Global finite results need **compactness**: either `X` is compact, or the relevant set (`Z(𝔞)`, `V`, `W`) is compact; otherwise the results hold over open sets contained in a compact set, or over a **relatively compact** neighbourhood of any compact set.

Vocabulary (all in this library): `GermIdeal n X` is an ideal sheaf of holomorphic germs, with `IsCoherent`, `zeroLocus` (`Z(𝔞)`), `pullback`; `EffectiveDivisor` is an invertible ideal sheaf `𝒪(-D)` with its support; `ClosedIrreducibleAnalyticSubvariety` and `IsComplexAnalyticSubset` are analytic subsets; `Hironaka.singularLocus V = V \ V_reg` (`V_sing`), and `W_sing = W \ regularLocus W d`; `IsSNCDivisor n E` says that the closed members of the list `E` have simple normal crossings (at every point the members through it are distinct coordinate hyperplanes of one chart); an *admissible blowup sequence* of `(X, E₀)` over `F` (`HironakaAdmissibleSequence.IsAdmissibleBlowupSequence n X E₀ F X' f E`) is a finite composition `f : X' → X` of blowups with smooth centres, each centre having only normal crossings with the divisor accumulated so far and lying over `F`; `E` starts with the strict transforms of the members of `E₀`, then has one member per blowup. `exceptionalLocus` (`Exc f`), `strictTransform` and `IsIsomorphismOver` have their usual meaning.

## What is proved

The public surface is the 42 theorems of the modules `Hironaka.API`, `Hironaka.API2`, `Hironaka.API3`, `Hironaka.API4`. They are restatements, with the internal machinery hidden, of the theorems of the `Hironaka.Resolution.*` modules. All of them are stated in the namespace `Hironaka`.

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

## Known gaps with respect to the standard theorems

The theorems are honest statements of what is proved, but they are weaker than the strongest classical forms in the
following respects.

1. **Scope.** The ambient space is always a complex manifold (smooth); singular analytic spaces appear only as analytic
   subsets of a manifold (embedded resolution) or through ideal sheaves (principalization). There is no statement about
   abstract analytic spaces, algebraic varieties, schemes, or fields other than `ℂ`.
2. **No functoriality in the elementary statements.** They are existence statements. At the marked-ideal level,
   `Hironaka.canonicalResolution` gives compatibility with restriction to open sets and uniqueness up to isomorphism under
   biholomorphisms of the base, but nothing about general smooth morphisms, and the elementary theorems do not say that
   their `f` is the canonical one.
3. **Compactness.** A finite blowup sequence is produced when `X` is compact, or when `Z(𝔞)` (resp. `V`, `W`) is
   compact; otherwise only over an open set contained in a compact set, or over a relatively compact neighbourhood of a
   compact set. There is no locally finite global sequence on a non-compact manifold (the form of Bierstone--Milman 1997
   for non-compact spaces).
4. **Embedded resolution relative to a boundary: the sharp form is not proved** (`*_boundary*`). The centres lie over
   `F = W_sing ∪ (W ∩ |E₀|)`, so `f` may blow up points where `W` is smooth and has normal crossings with `E₀`. The sharp
   form -- no blowup over the locus where `W` is smooth and has normal crossings with `E₀` -- is a known gap, deferred to
   a later release; it would need the modified invariant of Bierstone--Milman 1997, Section 12. Bierstone--Milman 1997,
   Theorem 1.6 itself has the same behaviour (their Remark 1.7 (3)). Only `Exc f ⊆ ⋃ (new members) ⊆ f⁻¹ F` is stated, not equality. Hypothesis:
   no member of `E₀` contains a nonempty relatively open subset of `W`.
5. **Analytic sets that are not equidimensional.** One admissible sequence resolves an analytic set `W` with empty
   interior whose components may have different dimensions (`Hironaka.exists_embeddedResolution_analytic*`), with
   smooth, pairwise disjoint strict transforms of the dimension parts `W⁽ᵏ⁾ = closure (Reg_k W)`: for compact `W` (or
   compact `X`), and for any `W` over an open set contained in a compact set or over a relatively compact neighbourhood of
   a compact set (as in item 3, there is no locally finite global sequence). `interior W = ∅` is assumed (no
   `n`-dimensional part). The identification of `W⁽ᵏ⁾` with the union of the `k`-dimensional irreducible components is
   not stated.
6. **The divisor of principalization** is not stated to be a combination `Σ aᵢ Eᵢ` of the members of `E`; only
   `Supp D = ⋃ E` (resp. `⋃ E.drop |E₀|`) is stated.
7. **Simultaneous normal crossings.** `HasNormalCrossings S E` allows `S` to lie inside a member of `E`. For an
   irreducible `V` this is excluded by connectedness and `⋃ E ⊆ f⁻¹(V_sing)`, but this is not stated as a theorem; for the
   pure-dimensional and boundary forms it is not stated.
8. **Position of the centres.** Every embedded form states that the centres lie over the singular set (`W_sing`, resp.
   `F`) and that `f` is an isomorphism over the complement. The literal condition "`Cⱼ ⊂ Sing Xⱼ`, or `Xⱼ` smooth and
   `Cⱼ ⊂ Xⱼ ∩ Eⱼ`" of Bierstone--Milman 1997, Theorem 1.6 (1) (Bierstone--Milman 2008, (2′)), on the current strict
   transform, is not stated.
9. **Normal crossings.** The output divisors have *simple* normal crossings (stronger than normal crossings), and an
   initial boundary `E₀` must have simple normal crossings.

## Building

You need [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.33.1`) and Mathlib is pinned to commit `0df444a360eaa60ab8c11dca51a86af692955474` (tag `v4.33.1`) in `lakefile.toml` and `lake-manifest.json`.

```sh
lake exe cache get      # download the compiled Mathlib
lake build              # build the library
lake test               # print and check the axioms (scripts/CheckAxioms.lean)
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

Every declaration of the library, and in particular every public theorem, depends only on the three standard axioms of Lean and Mathlib: `propext`, `Classical.choice` and `Quot.sound`. The library declares no axioms of its own, and `scripts/CheckAxioms.lean` checks this for every declaration.

## Verification

Performed on this release (352 modules, 3557 declarations, 94679 lines of Lean):

* **Build**: `lake build` from scratch: exit code 0, 352 modules compiled, 0 errors, 0 warnings, 0 declarations with an incomplete proof, 2470 s with one Lean process at a time.
* **Axioms**: `#print axioms` on each of the 42 public theorems and `collectAxioms` on all 4439 declarations: every public theorem depends exactly on `Classical.choice`, `Quot.sound`, `propext`; all 4439 declarations depend on these three at most.
* **Faithfulness**: every declaration of the library was compared with the declaration it was extracted from, in one Lean environment containing both (types, definition bodies and inductive types, up to the renaming of names): 42/42 public theorem statements equal; of the 4438 compared declarations, 4435 are syntactically equal and 3 equal up to definitional unfolding (all of them differ only in the numbering of `_proof_N` auxiliary lemmas), 0 differ; the 24 further declarations of the library (generated or auxiliary) all have an equal original (0 exceptions); 3522/3531 proof terms identical.
* **Kernel replay**: `leanchecker` on all 352 modules: exit code 0, 352 modules replayed, 0 problems.
* **Source scan**: 359 files scanned for e-mail addresses, incomplete-proof markers, declarations of axioms, kernel-bypassing tactics, internal identifiers and internal paths: 0 hits.

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

Some docstrings refer to statements of the LaTeX write-up from which the formalization was developed by labels such as `hir:general-step`; that write-up is not part of this repository. Labels such as `pr:resol` or `le:S` are those of the arXiv source of Włodarczyk 2005, and keys such as `wlodarczyk05-hironaka` refer to the references below.

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

Authors: Claude. The library was written by AI agents (Claude, by Anthropic) formalizing in Lean 4 with Mathlib. It is released under the Apache License 2.0 (see `LICENSE`).
