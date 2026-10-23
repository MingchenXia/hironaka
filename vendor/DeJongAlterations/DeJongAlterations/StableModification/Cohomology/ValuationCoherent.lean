/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.ValuationLaurent
import DeJongAlterations.StableModification.ValuationRing.Nagata

/-!
# Coordinate Čech cohomology of finitely presented graded modules over a valuation ring

Let `V` be a valuation ring (not necessarily Noetherian), `I` a finite linearly ordered set and
`M` a finitely presented graded `V[T_i]_{i ∈ I}`-module. Then every cohomology module of the
coordinate Čech complex of `M` (the complex `S ↦ (M_{T_S})_k` computing the cohomology of the
twisted sheaf `M~(k)` on `ℙ^I_V`) is a finitely presented `V`-module
(`finitePresentation_homogeneousCoordinateCech_homology`).

This replaces Temkin's appeal to Noetherian approximation (Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010), proof of Proposition 4.4.6, `semi-stable.tex`
lines 3215–3219: "the cited results are formulated in noetherian setting, so we use noetherian
approximation") by coherence: `V` and the finitely presented `V`-algebra `V[T]` are coherent rings
(`ValuationRing.Nagata`, `cor:sm-fp-coherent`: kernels of maps of finitely presented modules are
finitely presented). The proof is a descending induction on the degree, as in Codex's Noetherian
proof (`homogeneousCoordinateCech_homology_finite_dimensionInduction`), but with two steps of a
graded free resolution `F₁ → F₀ → M → 0`:

* from `0 → K₁ → F₁ → K₀ → 0` the cohomology `Hᵖ(K₀)` is finitely generated, because it sits
  between the image of `Hᵖ(F₁)` and the kernel of `H^{p+1}(K₁) → H^{p+1}(F₁)`
  (`finite_of_exact_four`);
* from `0 → K₀ → F₀ → M → 0` the cohomology `Hᵖ(M)` is an extension of the kernel of
  `H^{p+1}(K₀) → H^{p+1}(F₀)` by `Hᵖ(F₀)` modulo the finitely generated image of `Hᵖ(K₀)`, hence
  finitely presented (`finitePresentation_of_exact_five`).

The free modules are handled in `ValuationLaurent.lean`. Blueprint: `sm-cohomology-valuation.tex`,
`lem:sm-val-coherent-exact`, `thm:sm-val-graded-fp`.
-/

universe u

open CategoryTheory
open DeJongAlterations.Geometry.ProperSteinProjectiveCech
open DeJongAlterations.StableModification.ValuationRing

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

section CoherentModules

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
variable {A B C D E : Type u} [AddCommGroup A] [Module V A] [AddCommGroup B] [Module V B]
  [AddCommGroup C] [Module V C] [AddCommGroup D] [Module V D] [AddCommGroup E] [Module V E]

/-- Over a valuation ring, kernels of maps between finitely presented modules are finitely
presented (`V` is coherent, `cor:sm-fp-coherent`). -/
theorem finitePresentation_ker_valuation [Module.FinitePresentation V D]
    [Module.FinitePresentation V E] (γ : D →ₗ[V] E) :
    Module.FinitePresentation V (LinearMap.ker γ) :=
  finitePresentation_ker_of_finitePresentation V (A := V) γ

omit [IsDomain V] [ValuationRing V] in
/-- The corestriction of `b` to the kernel of the next map of an exact sequence, and its
surjectivity. -/
private lemma surjective_codRestrict_ker {b : C →ₗ[V] D} {γ : D →ₗ[V] E}
    (h : Function.Exact b γ) :
    Function.Surjective (b.codRestrict (LinearMap.ker γ) fun c => h.apply_apply_eq_zero c) := by
  rintro ⟨d, hd⟩
  obtain ⟨c, rfl⟩ := (h d).mp hd
  exact ⟨c, rfl⟩

/-- **Finite generation in a four-term exact sequence.** Over a valuation ring, if
`X → Y → Z → W` is exact at `Y` and `Z`, `X` is finitely generated and `Z`, `W` are finitely
presented, then `Y` is finitely generated. -/
theorem finite_of_exact_four (β : A →ₗ[V] B) (e : B →ₗ[V] C) (γ : C →ₗ[V] D)
    (h₁ : Function.Exact β e) (h₂ : Function.Exact e γ) [Module.Finite V A]
    [Module.FinitePresentation V C] [Module.FinitePresentation V D] : Module.Finite V B := by
  have := finitePresentation_ker_valuation γ
  let e' : B →ₗ[V] LinearMap.ker γ := e.codRestrict (LinearMap.ker γ) fun c => h₂.apply_apply_eq_zero c
  have he' : Function.Exact β e' := fun b => by
    rw [← h₁ b]
    exact Subtype.ext_iff
  exact Module.Finite.of_exact he' (surjective_codRestrict_ker h₂)

/-- **Finite presentation in a five-term exact sequence.** Over a valuation ring, if
`A → B → C → D → E` is exact at `B`, `C`, `D`, `A` is finitely generated and `B`, `D`, `E` are
finitely presented, then `C` is finitely presented. -/
theorem finitePresentation_of_exact_five (α : A →ₗ[V] B) (a : B →ₗ[V] C) (b : C →ₗ[V] D)
    (γ : D →ₗ[V] E) (h₁ : Function.Exact α a) (h₂ : Function.Exact a b) (h₃ : Function.Exact b γ)
    [Module.Finite V A] [Module.FinitePresentation V B] [Module.FinitePresentation V D]
    [Module.FinitePresentation V E] : Module.FinitePresentation V C := by
  have := finitePresentation_ker_valuation γ
  let b' : C →ₗ[V] LinearMap.ker γ := b.codRestrict (LinearMap.ker γ) fun c => h₃.apply_apply_eq_zero c
  have hker : LinearMap.ker b' = LinearMap.range a := by
    ext c
    rw [LinearMap.mem_ker, LinearMap.mem_range, ← Set.mem_range, ← h₂ c]
    exact Subtype.ext_iff
  have hra : Module.FinitePresentation V (LinearMap.range a) := by
    refine Module.finitePresentation_of_surjective a.rangeRestrict a.surjective_rangeRestrict ?_
    rw [LinearMap.ker_rangeRestrict, LinearMap.exact_iff.mp h₁, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map α
  have : Module.FinitePresentation V (LinearMap.ker b') :=
    Module.FinitePresentation.of_equiv (LinearEquiv.ofEq _ _ hker).symm
  exact Module.finitePresentation_of_ker b' (surjective_codRestrict_ker h₃)

end CoherentModules

section HomogeneousGenerators

variable {K R M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ]

omit [Algebra K R] in
/-- A finitely generated graded module is generated by finitely many homogeneous elements (the
homogeneous components of any finite set of generators). -/
theorem exists_homogeneous_span_eq_top [Module.Finite R M] :
    ∃ s : Finset M, (∀ m ∈ s, ∃ d, m ∈ ℳ d) ∧ Submodule.span R (s : Set M) = ⊤ := by
  classical
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := R) (M := M)
  refine ⟨t.biUnion fun m => (DirectSum.decompose ℳ m).support.image
    fun d => (DirectSum.decompose ℳ m d : M), ?_, ?_⟩
  · intro m hm
    obtain ⟨m', -, hm'⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hm'
    exact ⟨d, (DirectSum.decompose ℳ m' d).property⟩
  · rw [eq_top_iff, ← ht, Submodule.span_le]
    intro m hm
    rw [← DirectSum.sum_support_decompose ℳ m]
    refine Submodule.sum_mem _ fun d hd => Submodule.subset_span ?_
    exact Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩

omit [Algebra K R] in
/-- A finite homogeneous presentation map onto a finitely generated graded module. -/
theorem exists_homogeneousPresentation [Module.Finite R M] :
    ∃ (s : Finset M) (δ : s → ℤ), (∀ i : s, (i : M) ∈ ℳ (δ i)) ∧
      Function.Surjective (finiteHomogeneousPresentationMap (R := R) (fun i : s => (i : M))) := by
  obtain ⟨s, hs, hspan⟩ := exists_homogeneous_span_eq_top (R := R) ℳ
  choose δ hδ using fun i : s => hs i i.property
  refine ⟨s, δ, hδ, finiteHomogeneousPresentationMap_surjective _ ?_⟩
  rw [← hspan]
  congr 1
  ext m
  simp

end HomogeneousGenerators

section Graded

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
variable {I : Type u} [LinearOrder I] [Fintype I]

omit [IsDomain V] [ValuationRing V] in
/-- Exactness of a `ModuleCat` short complex as exactness of functions. -/
private lemma function_exact {S : ShortComplex (ModuleCat.{u} V)} (h : S.Exact) :
    Function.Exact S.f.hom S.g.hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp h

variable (V I) in
/-- The descending induction behind `finitePresentation_homogeneousCoordinateCech_homology`. -/
theorem finitePresentation_homogeneousCoordinateCech_homology_aux (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module V M] [Module (MvPolynomial I V) M]
      [IsScalarTower V (MvPolynomial I V) M] (ℳ : ℤ → Submodule V M) [DirectSum.Decomposition ℳ]
      [SetLike.GradedSMul (polynomialIntegralGrading (K := V) (I := I)) ℳ]
      [Module.FinitePresentation (MvPolynomial I V) M] (k : ℤ) (p : ℕ),
      Fintype.card I ≤ p + n →
      Module.FinitePresentation V ((homogeneousCoordinateCechComplex
        (polynomialIntegralGrading (K := V) (I := I)) ℳ
        (fun i => (MvPolynomial.X i : MvPolynomial I V)) polynomialCoordinate_X_degree k).homology
          p) := by
  classical
  induction n with
  | zero =>
    intro M _ _ _ _ ℳ _ _ _ k p hp
    have : Subsingleton ((homogeneousCoordinateCechComplex
        (polynomialIntegralGrading (K := V) (I := I)) ℳ
        (fun i => (MvPolynomial.X i : MvPolynomial I V)) polynomialCoordinate_X_degree k).homology
          p) :=
      ModuleCat.subsingleton_of_isZero
        (subsetCechComplex_homology_isZero_of_card_le _ p (by simpa using hp))
    exact Module.FinitePresentation.of_subsingleton _
  | succ n ih =>
    intro M _ _ _ _ ℳ _ _ _ k p hp
    let 𝒜 := polynomialIntegralGrading (K := V) (I := I)
    let x := fun i => (MvPolynomial.X i : MvPolynomial I V)
    have hx : ∀ i, x i ∈ 𝒜 1 := polynomialCoordinate_X_degree
    -- the first step of a graded free resolution `F₀ → M`
    obtain ⟨s, δ, hg, hsurj⟩ := exists_homogeneousPresentation (R := MvPolynomial I V) ℳ
    let f₀ := finiteHomogeneousPresentationMap (R := MvPolynomial I V) (fun i : s => (i : M))
    have hf₀ := finiteHomogeneousPresentationMap_homogeneous 𝒜 ℳ δ (fun i : s => (i : M)) hg
    let ℱ₀ := finiteShiftedFreePiece 𝒜 δ
    let ℒ₀ := homogeneousSubmodulePiece ℱ₀ (LinearMap.ker f₀)
    let _ : DirectSum.Decomposition ℒ₀ := actualHomogeneousKernelDecomposition ℱ₀ ℳ f₀ hf₀
    have : Module.FinitePresentation (MvPolynomial I V) (LinearMap.ker f₀) :=
      finitePresentation_ker_of_finitePresentation V (A := MvPolynomial I V) f₀
    -- the second step `F₁ → K₀`
    obtain ⟨s₁, δ₁, hg₁, hsurj₁⟩ :=
      exists_homogeneousPresentation (R := MvPolynomial I V) ℒ₀
    let f₁ := finiteHomogeneousPresentationMap (R := MvPolynomial I V)
      (fun i : s₁ => (i : LinearMap.ker f₀))
    have hf₁ := finiteHomogeneousPresentationMap_homogeneous 𝒜 ℒ₀ δ₁
      (fun i : s₁ => (i : LinearMap.ker f₀)) hg₁
    let ℱ₁ := finiteShiftedFreePiece 𝒜 δ₁
    let ℒ₁ := homogeneousSubmodulePiece ℱ₁ (LinearMap.ker f₁)
    let _ : DirectSum.Decomposition ℒ₁ := actualHomogeneousKernelDecomposition ℱ₁ ℒ₀ f₁ hf₁
    have : Module.FinitePresentation (MvPolynomial I V) (LinearMap.ker f₁) :=
      finitePresentation_ker_of_finitePresentation V (A := MvPolynomial I V) f₁
    -- the short exact sequences of coordinate Čech complexes
    let S₁ := actualHomogeneousKernelCechShortComplex 𝒜 ℱ₀ ℳ x hx f₀ hf₀ k
    have hS₁ : S₁.ShortExact :=
      actualHomogeneousKernelCechShortComplex_shortExact 𝒜 ℱ₀ ℳ x hx f₀ hf₀ hsurj k
    let S₂ := actualHomogeneousKernelCechShortComplex 𝒜 ℱ₁ ℒ₀ x hx f₁ hf₁ k
    have hS₂ : S₂.ShortExact :=
      actualHomogeneousKernelCechShortComplex_shortExact 𝒜 ℱ₁ ℒ₀ x hx f₁ hf₁ hsurj₁ k
    have hrel : (ComplexShape.up ℕ).Rel p (p + 1) := rfl
    -- finiteness inputs
    have hF₀p : Module.FinitePresentation V (S₁.X₂.homology p) :=
      finitePresentation_shiftedFree_homology δ k p
    have hF₀p' : Module.FinitePresentation V (S₁.X₂.homology (p + 1)) :=
      finitePresentation_shiftedFree_homology δ k (p + 1)
    have hF₁p : Module.FinitePresentation V (S₂.X₂.homology p) :=
      finitePresentation_shiftedFree_homology δ₁ k p
    have hF₁p' : Module.FinitePresentation V (S₂.X₂.homology (p + 1)) :=
      finitePresentation_shiftedFree_homology δ₁ k (p + 1)
    have hK₀p' : Module.FinitePresentation V (S₁.X₁.homology (p + 1)) :=
      ih (LinearMap.ker f₀) ℒ₀ k (p + 1) (by omega)
    have hK₁p' : Module.FinitePresentation V (S₂.X₁.homology (p + 1)) :=
      ih (LinearMap.ker f₁) ℒ₁ k (p + 1) (by omega)
    -- `Hᵖ(K₀)` is finitely generated
    have hK₀p : Module.Finite V (S₂.X₃.homology p) :=
      finite_of_exact_four (HomologicalComplex.homologyMap S₂.g p).hom (hS₂.δ p (p + 1) hrel).hom
        (HomologicalComplex.homologyMap S₂.f (p + 1)).hom
        (function_exact (hS₂.homology_exact₃ p (p + 1) hrel))
        (function_exact (hS₂.homology_exact₁ p (p + 1) hrel))
    have hK₀p₁ : Module.Finite V (S₁.X₁.homology p) := hK₀p
    -- `Hᵖ(M)` is finitely presented
    exact finitePresentation_of_exact_five (HomologicalComplex.homologyMap S₁.f p).hom
      (HomologicalComplex.homologyMap S₁.g p).hom (hS₁.δ p (p + 1) hrel).hom
      (HomologicalComplex.homologyMap S₁.f (p + 1)).hom
      (function_exact (hS₁.homology_exact₂ p))
      (function_exact (hS₁.homology_exact₃ p (p + 1) hrel))
      (function_exact (hS₁.homology_exact₁ p (p + 1) hrel))

/-- **Coherent cohomology of graded modules over a valuation ring**
(blueprint `thm:sm-val-graded-fp`): for a valuation ring `V`, a finite linearly ordered `I` and a
finitely presented graded `V[T_i]_{i ∈ I}`-module `M`, every cohomology module of the coordinate
Čech complex of `M` in every twisting degree `k` is a finitely presented `V`-module. -/
theorem finitePresentation_homogeneousCoordinateCech_homology (M : Type u) [AddCommGroup M]
    [Module V M] [Module (MvPolynomial I V) M] [IsScalarTower V (MvPolynomial I V) M]
    (ℳ : ℤ → Submodule V M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (polynomialIntegralGrading (K := V) (I := I)) ℳ]
    [Module.FinitePresentation (MvPolynomial I V) M] (k : ℤ) (p : ℕ) :
    Module.FinitePresentation V ((homogeneousCoordinateCechComplex
      (polynomialIntegralGrading (K := V) (I := I)) ℳ
      (fun i => (MvPolynomial.X i : MvPolynomial I V)) polynomialCoordinate_X_degree k).homology p) :=
  finitePresentation_homogeneousCoordinateCech_homology_aux V I (Fintype.card I) M ℳ k p
    (by omega)

end Graded

end

end DeJongAlterations.StableModification.Cohomology
