/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.Valuation

/-!
# Cohomology of projective schemes over a finitely presented algebra over a valuation ring

Let `V` be a valuation ring and `R` a finitely presented `V`-algebra (for instance the ring of an
affine open of a finitely presented `V`-curve). For projective coordinates on `X` over `R` and a
quasi-coherent `F` whose sections on the charts are finitely generated and have no `V`-torsion,
every Čech cohomology module `Ȟᵖ(U, F)` is a finitely presented `R`-module
(`ProjectiveCoordinates.finitePresentation_cechCohomology_fp`). This is lane COH3A's theorem
`finitePresentation_cechCohomology_valuation` (the case `R = V`) with the coefficient ring `V`
replaced by `R`; the proof is the same, because only two properties of the coefficient ring are
used:

* `R` and `R[T₀, …, Tₙ]` are coherent rings: kernels of maps between finitely presented modules
  are finitely presented. This holds for every finitely presented `V`-algebra
  (`ValuationRing.finitePresentation_ker_of_finitePresentation`, the valuation-ring case of
  Raynaud–Gruson I 3.4.7, blueprint `cor:sm-fp-coherent`);
* a finitely generated `R[T]`-module without `V`-torsion is finitely presented
  (`finitePresentation_of_torsionFree`, from `ValuationRing.fg_of_saturated`).

It is the input of the finiteness of `π_* 𝒪_B` for a projective morphism `π : B → Y` of
`V`-curves (`SteinFinite.lean`), which replaces Temkin's Lemma 4.4.1 and its use of the reduced
fibre theorem (Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`semi-stable.tex` lines 3089–3104; plan `PLAN-SM-GEOM.md`, S8).

Blueprint: `sm-cohomology-stein.tex`, `lem:sm-fp-torsion-free`, `lem:sm-fp-exact`,
`thm:sm-fp-graded`, `thm:sm-fp-cech`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry
open DeJongAlterations.Geometry.ProperSteinProjectiveCech
open DeJongAlterations.StableModification.ValuationRing

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

section TorsionFree

variable (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]

/-- **Finitely generated modules without `V`-torsion are finitely presented** over a
`V`-algebra of finite type (Raynaud–Gruson I 3.4.7 for valuation rings, in the form
`ValuationRing.fg_of_saturated`: the kernel of a presentation `Aⁿ → M` is saturated). -/
theorem finitePresentation_of_torsionFree {A M : Type*} [CommRing A] [Algebra V A]
    [Algebra.FiniteType V A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (htf : ∀ c : V, c ≠ 0 → ∀ m : M, algebraMap V A c • m = 0 → m = 0) :
    Module.FinitePresentation A M := by
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' A M
  refine Module.finitePresentation_of_surjective φ hφ
    (fg_of_saturated (V := V) _ fun c hc x hx => ?_)
  rw [LinearMap.mem_ker] at hx ⊢
  have hcx : c • x = algebraMap V A c • x := funext fun j => Algebra.smul_def c (x j)
  rw [hcx, map_smul] at hx
  exact htf c hc _ hx

end TorsionFree

section CoherentModules

variable (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
variable {R : Type u} [CommRing R] [Algebra V R] [Algebra.FinitePresentation V R]
variable {A B C D E : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D] [AddCommGroup E] [Module R E]

omit [Algebra V R] [Algebra.FinitePresentation V R] in
/-- The corestriction of `b` to the kernel of the next map of an exact sequence is surjective. -/
private lemma surjective_codRestrict_ker {b : C →ₗ[R] D} {γ : D →ₗ[R] E}
    (h : Function.Exact b γ) :
    Function.Surjective (b.codRestrict (LinearMap.ker γ) fun c => h.apply_apply_eq_zero c) := by
  rintro ⟨d, hd⟩
  obtain ⟨c, rfl⟩ := (h d).mp hd
  exact ⟨c, rfl⟩

include V in
/-- **Finite generation in a four-term exact sequence** over a finitely presented algebra over a
valuation ring: if `X → Y → Z → W` is exact at `Y` and `Z`, `X` is finitely generated and `Z`,
`W` are finitely presented, then `Y` is finitely generated. -/
theorem finite_of_exact_four_fp (β : A →ₗ[R] B) (e : B →ₗ[R] C) (γ : C →ₗ[R] D)
    (h₁ : Function.Exact β e) (h₂ : Function.Exact e γ) [Module.Finite R A]
    [Module.FinitePresentation R C] [Module.FinitePresentation R D] : Module.Finite R B := by
  have := finitePresentation_ker_of_finitePresentation V (A := R) γ
  let e' : B →ₗ[R] LinearMap.ker γ :=
    e.codRestrict (LinearMap.ker γ) fun c => h₂.apply_apply_eq_zero c
  have he' : Function.Exact β e' := fun b => by
    rw [← h₁ b]
    exact Subtype.ext_iff
  exact Module.Finite.of_exact he' (surjective_codRestrict_ker h₂)

include V in
/-- **Finite presentation in a five-term exact sequence** over a finitely presented algebra over a
valuation ring: if `A → B → C → D → E` is exact at `B`, `C`, `D`, `A` is finitely generated and
`B`, `D`, `E` are finitely presented, then `C` is finitely presented. -/
theorem finitePresentation_of_exact_five_fp (α : A →ₗ[R] B) (a : B →ₗ[R] C) (b : C →ₗ[R] D)
    (γ : D →ₗ[R] E) (h₁ : Function.Exact α a) (h₂ : Function.Exact a b) (h₃ : Function.Exact b γ)
    [Module.Finite R A] [Module.FinitePresentation R B] [Module.FinitePresentation R D]
    [Module.FinitePresentation R E] : Module.FinitePresentation R C := by
  have := finitePresentation_ker_of_finitePresentation V (A := R) γ
  let b' : C →ₗ[R] LinearMap.ker γ :=
    b.codRestrict (LinearMap.ker γ) fun c => h₃.apply_apply_eq_zero c
  have hker : LinearMap.ker b' = LinearMap.range a := by
    ext c
    rw [LinearMap.mem_ker, LinearMap.mem_range, ← Set.mem_range, ← h₂ c]
    exact Subtype.ext_iff
  have hra : Module.FinitePresentation R (LinearMap.range a) := by
    refine Module.finitePresentation_of_surjective a.rangeRestrict a.surjective_rangeRestrict ?_
    rw [LinearMap.ker_rangeRestrict, LinearMap.exact_iff.mp h₁, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map α
  have : Module.FinitePresentation R (LinearMap.ker b') :=
    Module.FinitePresentation.of_equiv (LinearEquiv.ofEq _ _ hker).symm
  exact Module.finitePresentation_of_ker b' (surjective_codRestrict_ker h₃)

end CoherentModules

section Graded

variable (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
variable {R : Type u} [CommRing R] [Algebra V R] [Algebra.FinitePresentation V R]
variable {I : Type u} [LinearOrder I] [Fintype I]

omit [Algebra V R] [Algebra.FinitePresentation V R] [Fintype I] [LinearOrder I] in
/-- Exactness of a `ModuleCat` short complex as exactness of functions. -/
private lemma function_exact {S : ShortComplex (ModuleCat.{u} R)} (h : S.Exact) :
    Function.Exact S.f.hom S.g.hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp h

include V in
variable (R I) in
/-- The descending induction behind `finitePresentation_homogeneousCoordinateCech_homology_fp`
(the proof of `finitePresentation_homogeneousCoordinateCech_homology_aux` with coefficients in a
finitely presented `V`-algebra). -/
theorem finitePresentation_homogeneousCoordinateCech_homology_fp_aux (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module (MvPolynomial I R) M]
      [IsScalarTower R (MvPolynomial I R) M] (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
      [SetLike.GradedSMul (polynomialIntegralGrading (K := R) (I := I)) ℳ]
      [Module.FinitePresentation (MvPolynomial I R) M] (k : ℤ) (p : ℕ),
      Fintype.card I ≤ p + n →
      Module.FinitePresentation R ((homogeneousCoordinateCechComplex
        (polynomialIntegralGrading (K := R) (I := I)) ℳ
        (fun i => (MvPolynomial.X i : MvPolynomial I R)) polynomialCoordinate_X_degree k).homology
          p) := by
  classical
  induction n with
  | zero =>
    intro M _ _ _ _ ℳ _ _ _ k p hp
    have : Subsingleton ((homogeneousCoordinateCechComplex
        (polynomialIntegralGrading (K := R) (I := I)) ℳ
        (fun i => (MvPolynomial.X i : MvPolynomial I R)) polynomialCoordinate_X_degree k).homology
          p) :=
      ModuleCat.subsingleton_of_isZero
        (subsetCechComplex_homology_isZero_of_card_le _ p (by simpa using hp))
    exact Module.FinitePresentation.of_subsingleton _
  | succ n ih =>
    intro M _ _ _ _ ℳ _ _ _ k p hp
    let 𝒜 := polynomialIntegralGrading (K := R) (I := I)
    let x := fun i => (MvPolynomial.X i : MvPolynomial I R)
    have hx : ∀ i, x i ∈ 𝒜 1 := polynomialCoordinate_X_degree
    obtain ⟨s, δ, hg, hsurj⟩ := exists_homogeneousPresentation (R := MvPolynomial I R) ℳ
    let f₀ := finiteHomogeneousPresentationMap (R := MvPolynomial I R) (fun i : s => (i : M))
    have hf₀ := finiteHomogeneousPresentationMap_homogeneous 𝒜 ℳ δ (fun i : s => (i : M)) hg
    let ℱ₀ := finiteShiftedFreePiece 𝒜 δ
    let ℒ₀ := homogeneousSubmodulePiece ℱ₀ (LinearMap.ker f₀)
    let _ : DirectSum.Decomposition ℒ₀ := actualHomogeneousKernelDecomposition ℱ₀ ℳ f₀ hf₀
    have : Module.FinitePresentation (MvPolynomial I R) (LinearMap.ker f₀) :=
      finitePresentation_ker_of_finitePresentation V (A := MvPolynomial I R) f₀
    obtain ⟨s₁, δ₁, hg₁, hsurj₁⟩ :=
      exists_homogeneousPresentation (R := MvPolynomial I R) ℒ₀
    let f₁ := finiteHomogeneousPresentationMap (R := MvPolynomial I R)
      (fun i : s₁ => (i : LinearMap.ker f₀))
    have hf₁ := finiteHomogeneousPresentationMap_homogeneous 𝒜 ℒ₀ δ₁
      (fun i : s₁ => (i : LinearMap.ker f₀)) hg₁
    let ℱ₁ := finiteShiftedFreePiece 𝒜 δ₁
    let ℒ₁ := homogeneousSubmodulePiece ℱ₁ (LinearMap.ker f₁)
    let _ : DirectSum.Decomposition ℒ₁ := actualHomogeneousKernelDecomposition ℱ₁ ℒ₀ f₁ hf₁
    have : Module.FinitePresentation (MvPolynomial I R) (LinearMap.ker f₁) :=
      finitePresentation_ker_of_finitePresentation V (A := MvPolynomial I R) f₁
    let S₁ := actualHomogeneousKernelCechShortComplex 𝒜 ℱ₀ ℳ x hx f₀ hf₀ k
    have hS₁ : S₁.ShortExact :=
      actualHomogeneousKernelCechShortComplex_shortExact 𝒜 ℱ₀ ℳ x hx f₀ hf₀ hsurj k
    let S₂ := actualHomogeneousKernelCechShortComplex 𝒜 ℱ₁ ℒ₀ x hx f₁ hf₁ k
    have hS₂ : S₂.ShortExact :=
      actualHomogeneousKernelCechShortComplex_shortExact 𝒜 ℱ₁ ℒ₀ x hx f₁ hf₁ hsurj₁ k
    have hrel : (ComplexShape.up ℕ).Rel p (p + 1) := rfl
    have hF₀p : Module.FinitePresentation R (S₁.X₂.homology p) :=
      finitePresentation_shiftedFree_homology δ k p
    have hF₀p' : Module.FinitePresentation R (S₁.X₂.homology (p + 1)) :=
      finitePresentation_shiftedFree_homology δ k (p + 1)
    have hF₁p : Module.FinitePresentation R (S₂.X₂.homology p) :=
      finitePresentation_shiftedFree_homology δ₁ k p
    have hF₁p' : Module.FinitePresentation R (S₂.X₂.homology (p + 1)) :=
      finitePresentation_shiftedFree_homology δ₁ k (p + 1)
    have hK₀p' : Module.FinitePresentation R (S₁.X₁.homology (p + 1)) :=
      ih (LinearMap.ker f₀) ℒ₀ k (p + 1) (by omega)
    have hK₁p' : Module.FinitePresentation R (S₂.X₁.homology (p + 1)) :=
      ih (LinearMap.ker f₁) ℒ₁ k (p + 1) (by omega)
    have hK₀p : Module.Finite R (S₂.X₃.homology p) :=
      finite_of_exact_four_fp V (HomologicalComplex.homologyMap S₂.g p).hom
        (hS₂.δ p (p + 1) hrel).hom (HomologicalComplex.homologyMap S₂.f (p + 1)).hom
        (function_exact (hS₂.homology_exact₃ p (p + 1) hrel))
        (function_exact (hS₂.homology_exact₁ p (p + 1) hrel))
    have hK₀p₁ : Module.Finite R (S₁.X₁.homology p) := hK₀p
    exact finitePresentation_of_exact_five_fp V (HomologicalComplex.homologyMap S₁.f p).hom
      (HomologicalComplex.homologyMap S₁.g p).hom (hS₁.δ p (p + 1) hrel).hom
      (HomologicalComplex.homologyMap S₁.f (p + 1)).hom
      (function_exact (hS₁.homology_exact₂ p))
      (function_exact (hS₁.homology_exact₃ p (p + 1) hrel))
      (function_exact (hS₁.homology_exact₁ p (p + 1) hrel))

include V in
/-- **Coordinate cohomology of finitely presented graded modules over a finitely presented
`V`-algebra** (blueprint `thm:sm-fp-graded`): for a finitely presented `V`-algebra `R`, a finite
linearly ordered `I` and a finitely presented graded `R[T_i]_{i ∈ I}`-module `M`, every cohomology
module of the coordinate Čech complex of `M` in every twisting degree is a finitely presented
`R`-module. -/
theorem finitePresentation_homogeneousCoordinateCech_homology_fp (M : Type u) [AddCommGroup M]
    [Module R M] [Module (MvPolynomial I R) M] [IsScalarTower R (MvPolynomial I R) M]
    (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (polynomialIntegralGrading (K := R) (I := I)) ℳ]
    [Module.FinitePresentation (MvPolynomial I R) M] (k : ℤ) (p : ℕ) :
    Module.FinitePresentation R ((homogeneousCoordinateCechComplex
      (polynomialIntegralGrading (K := R) (I := I)) ℳ
      (fun i => (MvPolynomial.X i : MvPolynomial I R)) polynomialCoordinate_X_degree k).homology
        p) :=
  finitePresentation_homogeneousCoordinateCech_homology_fp_aux V R I (Fintype.card I) M ℳ k p
    (by omega)

end Graded

section Serre

set_option backward.isDefEq.respectTransparency false

variable (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
variable {X : Scheme.{u}} {R : Type u} [CommRing R] [Algebra V R] [Algebra.FinitePresentation V R]
  {c : R →+* Γ(X, ⊤)}

namespace ProjectiveCoordinates

variable (D : ProjectiveCoordinates X R c) (F : X.Modules) [F.IsQuasicoherent]
  (hF : ∀ i, Module.Finite Γ(X, D.U i) Γ(F, D.U i))
  (htf : ∀ i, ∀ v : V, v ≠ 0 → ∀ s : Γ(F, D.U i), D.const i (algebraMap V R v) • s = 0 → s = 0)

omit [IsDomain V] [ValuationRing V] [Algebra.FinitePresentation V R] [F.IsQuasicoherent] in
include htf in
/-- The ambient module `∏ Γ(U_i, F)[t]` of twisted sections has no `V`-torsion when the sections
on the charts have none. -/
theorem ambient_eq_zero_of_algebraMap_smul_eq_zero {v : V} (hv : v ≠ 0) (e : D.Ambient F)
    (he : algebraMap V R v • e = 0) : e = 0 := by
  ext i : 1
  apply PolynomialModule.coeff_injective
  ext n
  have h := congrArg (fun e : D.Ambient F => (e i).coeff n) he
  simp only [Ambient.coeff_smul', PolynomialModule.coeff_zero,
    Finsupp.coe_zero, Pi.zero_apply] at h
  simpa using htf i v hv _ h

include htf in
/-- **Serre's module is finitely presented** over `R[T]` when the sections of `F` on the charts are
finitely generated and have no `V`-torsion (`finitePresentation_of_torsionFree`). -/
theorem finitePresentation_serreModule_fp :
    Module.FinitePresentation (MvPolynomial D.ι R) (D.serreModule F hF) := by
  have := D.finite_serreModule F hF
  refine finitePresentation_of_torsionFree V fun v hv m hm => Subtype.ext ?_
  refine D.ambient_eq_zero_of_algebraMap_smul_eq_zero V F htf hv m.val ?_
  have h : (algebraMap V (MvPolynomial D.ι R) v) • (m : D.Ambient F) = 0 := by
    simpa using congrArg Subtype.val hm
  rw [MvPolynomial.algebraMap_apply, ← MvPolynomial.algebraMap_eq, algebraMap_smul] at h
  exact h

include hF htf in
/-- **Finite presentation of Čech cohomology over a finitely presented `V`-algebra** (blueprint
`thm:sm-fp-cech`): for projective coordinates over a finitely presented algebra `R` over a
valuation ring `V` and `F` quasi-coherent whose sections on the charts are finitely generated and
have no `V`-torsion, every `Ȟᵖ(U, F)` is a finitely presented `R`-module. -/
theorem finitePresentation_cechCohomology_fp (p : ℕ) :
    Module.FinitePresentation R (cechCohomology F D.U c p) := by
  let _ := D.serreDecomposition F hF
  have := D.finitePresentation_serreModule_fp V F hF htf
  have h := finitePresentation_homogeneousCoordinateCech_homology_fp V (R := R) (I := D.ι)
    (D.serreModule F hF) (D.serrePiece F hF) 0 p
  have : Module.FinitePresentation R ((subsetCechComplex (D.serreDiagram F hF)).homology p) := h
  let e := SubsetNonemptyComparison.complexIso (D.serreDiagram F hF) (cechDiagram F D.U c)
    (D.comparisonIso F hF) (D.comparisonIso_naturality F hF)
  exact Module.FinitePresentation.of_equiv (HomologicalComplex.homologyMapIso e p).toLinearEquiv

end ProjectiveCoordinates

end Serre

end

end DeJongAlterations.StableModification.Cohomology
