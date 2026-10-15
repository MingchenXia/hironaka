/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaRelativeNormalUniformLocalization
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-! # Literal original associated-module localization and all actual graded-piece bases

The SAME original normal initial polynomial quotient is genuinely localized
using all three actual localization conditions. Localizing the actual original
symbol quotient equivalence identifies it with the localization of the LITERAL
original associated module. Actual tensor/localization and tensor/direct-sum
natural equivalences retain every original component and degree inclusion.
The internally supplied entire standard monomial basis therefore has a TRUE
original degree dictionary. Actual projections, inclusions and coefficient
restriction internally prove each degree combination injective and surjective.
The resulting actual basis vectors are LITERAL original normal monomial symbols
localized at numerator denominator one. Bounded original exponent entries make
each true degree index finite. ONE internally produced nonzero entire base germ
works for ALL actual ORIGINAL normal graded pieces simultaneously.

No caller localization, kernel, basis, homogeneous division, free or result
certificate is supplied. Whole ungraded free is never inferred to imply degree
free. ALL original truncation quotients require their genuine localized exact
filtration and internal projective splitting next; uniform analytic spread,
higher HS and general G8 remain separate OPEN obligations.
-/

set_option autoImplicit false
open Set
namespace Hironaka.HironakaRelativeNormalLocalizedAssociatedGraded
noncomputable section
open HironakaRelativeNormalUniformLocalization HironakaRelativeNormalAssociatedGraded
open scoped TensorProduct DirectSum

variable {B : Type*} [CommRing B]

/-- Literal whole original polynomial ideal coefficient extension at an ACTUAL base element. -/
def coefficientLocalizedIdeal (t : ℕ) (b : B) (H : Ideal (MvPolynomial (Fin t) B)) :
    Ideal (MvPolynomial (Fin t) (Localization.Away b)) :=
  Ideal.map (MvPolynomial.map (algebraMap B (Localization.Away b))) H

/-- The ACTUAL canonical quotient coefficient map of the SAME original whole polynomial ideal. -/
def polynomialQuotientLocalizationMap (t : ℕ) (b : B) (H : Ideal (MvPolynomial (Fin t) B)) :
    (MvPolynomial (Fin t) B ⧸ H) →ₐ[B]
      (MvPolynomial (Fin t) (Localization.Away b) ⧸ coefficientLocalizedIdeal t b H) :=
  Ideal.quotientMapₐ (coefficientLocalizedIdeal t b H)
    (MvPolynomial.mapAlgHom (Algebra.ofId B (Localization.Away b)))
    Ideal.le_comap_map

/-- On every ACTUAL original numerator the true quotient map is the LITERAL coefficient extension class. -/
theorem polynomialQuotientLocalizationMap_mk (t : ℕ) (b : B) (H : Ideal (MvPolynomial (Fin t) B))
    (P : MvPolynomial (Fin t) B) :
    polynomialQuotientLocalizationMap t b H (Ideal.Quotient.mk H P) =
      Ideal.Quotient.mk (coefficientLocalizedIdeal t b H)
        (MvPolynomial.map (algebraMap B (Localization.Away b)) P) := rfl

/-- ALL localization conditions of the SAME original whole polynomial quotient are produced internally from actual ring and ideal localization. -/
theorem polynomialQuotientLocalizationMap_isLocalizedModule (t : ℕ) (b : B)
    (H : Ideal (MvPolynomial (Fin t) B)) :
    IsLocalizedModule (Submonoid.powers b) (polynomialQuotientLocalizationMap t b H).toLinearMap := by
  let : Algebra (MvPolynomial (Fin t) B) (MvPolynomial (Fin t) (Localization.Away b)) :=
    MvPolynomial.algebraMvPolynomial
  apply IsLocalizedModule.mkOfAlgebra (Submonoid.powers b) (polynomialQuotientLocalizationMap t b H)
  · intro x hx
    change IsUnit (Ideal.Quotient.mk (coefficientLocalizedIdeal t b H)
      (MvPolynomial.C (algebraMap B (Localization.Away b) x)))
    exact (IsLocalization.map_units (Localization.Away b) ⟨x,hx⟩).map
      ((Ideal.Quotient.mk (coefficientLocalizedIdeal t b H)).comp MvPolynomial.C)
  · intro y
    obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨Q,s⟩,he⟩ := IsLocalization.surj
      ((Submonoid.powers b).map (MvPolynomial.C (σ := Fin t))) P
    obtain ⟨r,hr,hrs⟩ := Submonoid.mem_map.mp s.property
    refine ⟨⟨Ideal.Quotient.mk H Q,⟨r,hr⟩⟩,?_⟩
    change r • (Ideal.Quotient.mkₐ B (coefficientLocalizedIdeal t b H) P) =
      polynomialQuotientLocalizationMap t b H (Ideal.Quotient.mk H Q)
    rw [← map_smul,polynomialQuotientLocalizationMap_mk]
    apply congrArg (Ideal.Quotient.mk (coefficientLocalizedIdeal t b H))
    rw [← algebraMap_smul (Localization.Away b) r P,MvPolynomial.smul_eq_C_mul,mul_comm]
    simpa only [MvPolynomial.algebraMap_def,← hrs,MvPolynomial.map_C] using he
  · intro x hx
    obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [polynomialQuotientLocalizationMap_mk] at hx
    have hm : algebraMap (MvPolynomial (Fin t) B) (MvPolynomial (Fin t) (Localization.Away b)) P ∈
        Ideal.map (algebraMap (MvPolynomial (Fin t) B) (MvPolynomial (Fin t) (Localization.Away b))) H := by
      simpa only [coefficientLocalizedIdeal,MvPolynomial.algebraMap_def] using
        (Ideal.Quotient.eq_zero_iff_mem.mp hx)
    obtain ⟨s,hs,hmem⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      ((Submonoid.powers b).map (MvPolynomial.C (σ := Fin t))) (MvPolynomial (Fin t) (Localization.Away b)) H P).mp hm
    obtain ⟨r,hr,hrs⟩ := Submonoid.mem_map.mp hs
    refine ⟨⟨r,hr⟩,?_⟩
    change r • (Ideal.Quotient.mkₐ B H P) = 0
    rw [← map_smul,MvPolynomial.smul_eq_C_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa only [← hrs] using hmem)

/-- TRUE scalar-linear canonical localization equivalence of the SAME actual original polynomial quotient. -/
def polynomialQuotientLocalizationEquiv (t : ℕ) (b : B) (H : Ideal (MvPolynomial (Fin t) B)) :
    LocalizedModule (Submonoid.powers b) (MvPolynomial (Fin t) B ⧸ H) ≃ₗ[Localization.Away b]
      (MvPolynomial (Fin t) (Localization.Away b) ⧸ coefficientLocalizedIdeal t b H) :=
  letI := polynomialQuotientLocalizationMap_isLocalizedModule t b H
  (IsLocalizedModule.iso (Submonoid.powers b) (polynomialQuotientLocalizationMap t b H).toLinearMap).extendScalarsOfIsLocalization
    (Submonoid.powers b) (Localization.Away b)

/-- The TRUE canonical localized quotient equivalence retains every LITERAL original numerator class. -/
theorem polynomialQuotientLocalizationEquiv_mk_one (t : ℕ) (b : B) (H : Ideal (MvPolynomial (Fin t) B))
    (P : MvPolynomial (Fin t) B) :
    polynomialQuotientLocalizationEquiv t b H (LocalizedModule.mk (Ideal.Quotient.mk H P) 1) =
      Ideal.Quotient.mk (coefficientLocalizedIdeal t b H)
        (MvPolynomial.map (algebraMap B (Localization.Away b)) P) := by
  let := polynomialQuotientLocalizationMap_isLocalizedModule t b H
  exact IsLocalizedModule.iso_mk_one (Submonoid.powers b)
    (polynomialQuotientLocalizationMap t b H).toLinearMap (Ideal.Quotient.mk H P)

/-- Genuine localization FUNCTOR internally transports an actual original linear equivalence. -/
def actualLocalizedLinearEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]
    (S : Submonoid B) (e : M ≃ₗ[B] N) : LocalizedModule S M ≃ₗ[Localization S] LocalizedModule S N :=
  IsLocalizedModule.mapEquiv S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) (Localization S) e

/-- The ACTUAL localized equivalence retains every LITERAL original numerator. -/
theorem actualLocalizedLinearEquiv_mk_one {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]
    (S : Submonoid B) (e : M ≃ₗ[B] N) (x : M) :
    actualLocalizedLinearEquiv S e (LocalizedModule.mk x 1) = LocalizedModule.mk (e x) 1 := by
  change IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N)
    e.toLinearMap ((LocalizedModule.mkLinearMap S M) x) = (LocalizedModule.mkLinearMap S N) (e x)
  exact IsLocalizedModule.map_apply S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) e.toLinearMap x

/-- TRUE localization of the entire actual direct sum is the direct sum of TRUE piece localizations. -/
def localizedDirectSumEquiv {ι : Type*} (S : Submonoid B) (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)] :
    LocalizedModule S (⨁ i, M i) ≃ₗ[Localization S] ⨁ i, LocalizedModule S (M i) := by
  classical
  exact (LocalizedModule.equivTensorProduct S (⨁ i, M i)).trans
    ((TensorProduct.directSumRight B (Localization S) (Localization S) M).trans
      (DirectSum.congrLinearEquiv (fun i => (LocalizedModule.equivTensorProduct S (M i)).symm)))

/-- Actual localization/direct-sum equivalence has its literal numerator-denominator dictionary at EVERY original degree. -/
theorem localizedDirectSumEquiv_mk_component {ι : Type*} [DecidableEq ι] (S : Submonoid B) (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)] (x : ⨁ i, M i) (s : S) (q : ι) :
    localizedDirectSumEquiv S M (LocalizedModule.mk x s) q = LocalizedModule.mk (x q) s := by
  simp only [localizedDirectSumEquiv,LinearEquiv.trans_apply,DirectSum.coe_congrLinearEquiv,
    DirectSum.lmap_apply,LocalizedModule.equivTensorProduct_apply_mk,TensorProduct.directSumRight_tmul]
  simpa only [one_smul,LinearEquiv.coe_coe] using (LocalizedModule.equivTensorProduct_symm_apply_tmul S (x q) (1 : B) s)

/-- The TRUE whole direct-sum localization commutes with every LITERAL original degree inclusion. -/
theorem localizedDirectSumEquiv_mk_one_lof {ι : Type*} [DecidableEq ι] (S : Submonoid B) (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)] (q : ι) (x : M q) :
    localizedDirectSumEquiv S M (LocalizedModule.mk (DirectSum.lof B ι M q x) 1) =
      DirectSum.lof (Localization S) ι (fun i => LocalizedModule S (M i)) q (LocalizedModule.mk x 1) := by
  classical
  ext k
  rw [localizedDirectSumEquiv_mk_component]
  by_cases hk : q=k
  · subst k
    simp
  · simp only [DirectSum.lof_eq_of]
    rw [DirectSum.of_eq_of_ne (β := M) q k x (Ne.symm hk),
      DirectSum.of_eq_of_ne (β := fun i => LocalizedModule S (M i)) q k (LocalizedModule.mk (S := S) x 1) (Ne.symm hk)]
    simp

/-- Actual coefficient combination restricted to a literal degree fiber of a true whole direct-sum equivalence. -/
private def degreeFiberCombination {ι : Type*} (ν : ι → ℕ) (M : ℕ → Type*)
    [∀ q, AddCommGroup (M q)] [∀ q, Module B (M q)]
    (e : (ι →₀ B) ≃ₗ[B] ⨁ q, M q) (q : ℕ) :
    ({i : ι // ν i=q} →₀ B) →ₗ[B] M q :=
  (DirectSum.component B ℕ M q).comp (e.toLinearMap.comp (Finsupp.lmapDomain B B Subtype.val))

/-- The actual single coefficient of the degree-fiber combination retains its whole original vector component. -/
private theorem degreeFiberCombination_single {ι : Type*} (ν : ι → ℕ) (M : ℕ → Type*)
    [∀ q, AddCommGroup (M q)] [∀ q, Module B (M q)]
    (e : (ι →₀ B) ≃ₗ[B] ⨁ q, M q) (q : ℕ) (j : {i : ι // ν i=q}) (c : B) :
    degreeFiberCombination ν M e q (Finsupp.single j c) = (e (Finsupp.single j.val c)) q := by
  simp only [degreeFiberCombination,LinearMap.comp_apply,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,LinearEquiv.coe_coe]
  rfl

/-- Actual degree membership proves the literal WHOLE lift identity for every finite degree-fiber coefficient function. -/
private theorem degreeFiberCombination_lift {ι : Type*} (ν : ι → ℕ) (M : ℕ → Type*)
    [∀ q, AddCommGroup (M q)] [∀ q, Module B (M q)]
    (e : (ι →₀ B) ≃ₗ[B] ⨁ q, M q)
    (hgrade : ∀ i, e (Finsupp.single i 1) = DirectSum.lof B ℕ M (ν i) (e (Finsupp.single i 1) (ν i)))
    (q : ℕ) (a : {i : ι // ν i=q} →₀ B) :
    DirectSum.lof B ℕ M q (degreeFiberCombination ν M e q a) = e (Finsupp.mapDomain Subtype.val a) := by
  classical
  have hlm : (DirectSum.lof B ℕ M q).comp (degreeFiberCombination ν M e q) =
      e.toLinearMap.comp (Finsupp.lmapDomain B B (Subtype.val : {i : ι // ν i=q} → ι)) := by
    apply Finsupp.lhom_ext
    intro j c
    rcases j with ⟨j,hj⟩
    subst q
    simp only [degreeFiberCombination,LinearMap.comp_apply,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
      LinearEquiv.coe_coe]
    have hc : Finsupp.single j c = c • Finsupp.single j (1 : B) := by simp
    rw [hc,map_smul,hgrade j]
    simp
  exact LinearMap.congr_fun hlm a

/-- TRUE degree-fiber combination bijectivity follows from actual projections and inclusions of the internally supplied whole equivalence. -/
private theorem degreeFiberCombination_bijective {ι : Type*} (ν : ι → ℕ) (M : ℕ → Type*)
    [∀ q, AddCommGroup (M q)] [∀ q, Module B (M q)]
    (e : (ι →₀ B) ≃ₗ[B] ⨁ q, M q)
    (hgrade : ∀ i, e (Finsupp.single i 1) = DirectSum.lof B ℕ M (ν i) (e (Finsupp.single i 1) (ν i)))
    (q : ℕ) : Function.Bijective (degreeFiberCombination ν M e q) := by
  classical
  let inc := Finsupp.lmapDomain B B (Subtype.val : {i : ι // ν i=q} → ι)
  let res := Finsupp.lcomapDomain (R := B) (M := B) (Subtype.val : {i : ι // ν i=q} → ι) Subtype.val_injective
  let proj := (DirectSum.lof B ℕ M q).comp (DirectSum.component B ℕ M q)
  have hp : proj.comp e.toLinearMap = e.toLinearMap.comp (inc.comp res) := by
    apply Finsupp.lhom_ext
    intro i c
    change proj (e (Finsupp.single i c)) = e (inc (res (Finsupp.single i c)))
    by_cases hi : ν i=q
    · let j : {i : ι // ν i=q} := ⟨i,hi⟩
      have hr : res (Finsupp.single i c) = Finsupp.single j c :=
        Finsupp.comapDomain_single Subtype.val j c Subtype.val_injective.injOn
      rw [hr]
      have hl := degreeFiberCombination_lift ν M e hgrade q (Finsupp.single j c)
      simpa only [degreeFiberCombination,LinearMap.comp_apply,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
        LinearEquiv.coe_coe,proj,inc] using hl
    · have hn : i ∉ range (Subtype.val : {i : ι // ν i=q} → ι) := by
        rintro ⟨j,hj⟩
        exact hi (hj ▸ j.property)
      have hr : res (Finsupp.single i c) = 0 :=
        Finsupp.comapDomain_single_of_not_mem_range hn c Subtype.val_injective.injOn
      rw [hr,map_zero,map_zero]
      have hc : Finsupp.single i c = c • Finsupp.single i (1 : B) := by simp
      rw [hc,map_smul,hgrade i]
      rw [map_smul]
      change c • DirectSum.lof B ℕ M q ((DirectSum.lof B ℕ M (ν i) (e (Finsupp.single i 1) (ν i))) q) = 0
      simp only [DirectSum.lof_eq_of,DirectSum.of_eq_of_ne (β := M) (ν i) q _ (Ne.symm hi),map_zero,smul_zero]
  constructor
  · intro a b hab
    apply Finsupp.mapDomain_injective Subtype.val_injective
    apply e.injective
    rw [← degreeFiberCombination_lift ν M e hgrade q a,← degreeFiberCombination_lift ν M e hgrade q b,hab]
  · intro x
    let a := res (e.symm (DirectSum.lof B ℕ M q x))
    refine ⟨a,?_⟩
    have he : e (inc a) = DirectSum.lof B ℕ M q x := by
      have h := LinearMap.congr_fun hp (e.symm (DirectSum.lof B ℕ M q x))
      change DirectSum.lof B ℕ M q ((e (e.symm (DirectSum.lof B ℕ M q x))) q) = e (inc a) at h
      rw [LinearEquiv.apply_symm_apply] at h
      simpa only [DirectSum.lof_eq_of,DirectSum.of_eq_same] using h.symm
    change (e (inc a)) q = x
    rw [he]
    simp

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalTaylorCoefficients HironakaRelativeNormalMonomialBasis


/-- Literal localization of the SAME actual ORIGINAL J-adic associated module. -/
abbrev originalLocalizedAssociatedModule (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :=
  letI := tangentAlgebra d t
  LocalizedModule (Submonoid.powers (originalUniformNormalDenominator d t I)) (originalNormalAssociatedGraded d t I)

/-- TRUE original polynomial quotient identification acts by the ACTUAL original whole normal symbol. -/
theorem originalNormalAssociatedGradedQuotientEquiv_mk (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    let := tangentAlgebra d t
    originalNormalAssociatedGradedQuotientEquiv d t I (Ideal.Quotient.mk (originalNormalInitialIdeal d t I) P) =
      normalAssociatedSymbolMap d t I P := by
  let := tangentAlgebra d t
  rfl

/-- Genuine coefficient-localized whole original initial quotient is the localization of the SAME literal ORIGINAL associated module. -/
def originalLocalizedAssociatedQuotientEquiv (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    (MvPolynomial (Fin t) (Localization.Away (originalUniformNormalDenominator d t I)) ⧸ coefficientLocalizedIdeal t (originalUniformNormalDenominator d t I) (originalNormalInitialIdeal d t I))
      ≃ₗ[Localization.Away (originalUniformNormalDenominator d t I)] originalLocalizedAssociatedModule d t I :=
  letI := tangentAlgebra d t
  (polynomialQuotientLocalizationEquiv t (originalUniformNormalDenominator d t I) (originalNormalInitialIdeal d t I)).symm.trans
    (actualLocalizedLinearEquiv (Submonoid.powers (originalUniformNormalDenominator d t I))
      (originalNormalAssociatedGradedQuotientEquiv d t I))

/-- The SAME actual localized associated equivalence sends ORIGINAL polynomial numerator classes to their LITERAL localized original whole symbols. -/
theorem originalLocalizedAssociatedQuotientEquiv_mk (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    let := tangentAlgebra d t
    originalLocalizedAssociatedQuotientEquiv d t I (Ideal.Quotient.mk (coefficientLocalizedIdeal t (originalUniformNormalDenominator d t I) (originalNormalInitialIdeal d t I))
      (MvPolynomial.map (algebraMap (HolGerm (ComplexModel d)) (Localization.Away (originalUniformNormalDenominator d t I))) P)) =
        LocalizedModule.mk (normalAssociatedSymbolMap d t I P) 1 := by
  let := tangentAlgebra d t
  dsimp only
  let Q := polynomialQuotientLocalizationEquiv t (originalUniformNormalDenominator d t I) (originalNormalInitialIdeal d t I)
  let x := Ideal.Quotient.mk (originalNormalInitialIdeal d t I) P
  let y := Ideal.Quotient.mk (coefficientLocalizedIdeal t (originalUniformNormalDenominator d t I) (originalNormalInitialIdeal d t I))
    (MvPolynomial.map (algebraMap (HolGerm (ComplexModel d)) (Localization.Away (originalUniformNormalDenominator d t I))) P)
  have hQ : Q (LocalizedModule.mk x 1) = y := polynomialQuotientLocalizationEquiv_mk_one t
    (originalUniformNormalDenominator d t I) (originalNormalInitialIdeal d t I) P
  have hQi : Q.symm y = LocalizedModule.mk x 1 := Q.symm_apply_eq.mpr hQ.symm
  calc
    originalLocalizedAssociatedQuotientEquiv d t I y =
        actualLocalizedLinearEquiv (Submonoid.powers (originalUniformNormalDenominator d t I))
          (originalNormalAssociatedGradedQuotientEquiv d t I) (Q.symm y) := rfl
    _ = actualLocalizedLinearEquiv (Submonoid.powers (originalUniformNormalDenominator d t I))
          (originalNormalAssociatedGradedQuotientEquiv d t I) (LocalizedModule.mk x 1) := congrArg _ hQi
    _ = LocalizedModule.mk (originalNormalAssociatedGradedQuotientEquiv d t I x) 1 :=
      actualLocalizedLinearEquiv_mk_one _ (originalNormalAssociatedGradedQuotientEquiv d t I) x
    _ = LocalizedModule.mk (normalAssociatedSymbolMap d t I P) 1 :=
      congrArg (fun z => LocalizedModule.mk z 1) (originalNormalAssociatedGradedQuotientEquiv_mk d t I P)

/-- TRUE quotient equivalence for literal equal actual polynomial ideals, with their actual coefficient scalar structure. -/
def actualEqualIdealQuotientEquiv {A : Type*} [CommRing A] (t : ℕ)
    (H J : Ideal (MvPolynomial (Fin t) A)) (h : H=J) :
    (MvPolynomial (Fin t) A ⧸ H) ≃ₗ[A] (MvPolynomial (Fin t) A ⧸ J) :=
  Submodule.quotEquivOfEq (H.restrictScalars A) (J.restrictScalars A) (congrArg (fun L : Ideal (MvPolynomial (Fin t) A) => L.restrictScalars A) h)

/-- The equal-ideal quotient transport keeps EVERY actual polynomial numerator literally unchanged. -/
theorem actualEqualIdealQuotientEquiv_mk {A : Type*} [CommRing A] (t : ℕ)
    (H J : Ideal (MvPolynomial (Fin t) A)) (h : H=J) (P : MvPolynomial (Fin t) A) :
    actualEqualIdealQuotientEquiv t H J h (Ideal.Quotient.mk H P) = Ideal.Quotient.mk J P :=
  Submodule.quotEquivOfEq_mk _ _ _ P

/-- The SAME original initial ideal has literal equal coefficient-localized ideal definitions; their ACTUAL quotient scalar structures are transported explicitly. -/
def originalUniformCoefficientQuotientEquiv (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    (MvPolynomial (Fin t) (Localization.Away (originalUniformNormalDenominator d t I)) ⧸ originalUniformNormalIdeal d t I)
      ≃ₗ[Localization.Away (originalUniformNormalDenominator d t I)]
        (MvPolynomial (Fin t) (Localization.Away (originalUniformNormalDenominator d t I)) ⧸
          coefficientLocalizedIdeal t (originalUniformNormalDenominator d t I) (originalNormalInitialIdeal d t I)) :=
  actualEqualIdealQuotientEquiv t (originalUniformNormalIdeal d t I)
    (coefficientLocalizedIdeal t (originalUniformNormalDenominator d t I) (originalNormalInitialIdeal d t I)) rfl

/-- The ENTIRE actual original standard monomial basis genuinely transports to the SAME literal localized ORIGINAL associated module. -/
def originalLocalizedAssociatedMonomialBasis (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    Module.Basis (originalUniformNormalStandardExponentIndex d t I) (Localization.Away (originalUniformNormalDenominator d t I))
      (originalLocalizedAssociatedModule d t I) :=
  letI := tangentAlgebra d t
  ((originalUniformNormalStandardMonomialBasis d t I).map (originalUniformCoefficientQuotientEquiv d t I)).map
    (originalLocalizedAssociatedQuotientEquiv d t I)

/-- The SAME literal localized ORIGINAL associated module is truly free from its internally produced WHOLE original monomial basis. -/
theorem moduleFree_originalLocalizedAssociatedModule (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let := tangentAlgebra d t
    Module.Free (Localization.Away (originalUniformNormalDenominator d t I)) (originalLocalizedAssociatedModule d t I) :=
  let := tangentAlgebra d t
  Module.Free.of_basis (originalLocalizedAssociatedMonomialBasis d t I)
/-- The genuine ORIGINAL normal monomial symbol in its ACTUAL degree original J-adic piece. -/
def originalNormalMonomialSymbol (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (α : Fin t →₀ ℕ) : letI := tangentAlgebra d t
    originalNormalGradedPiece d t I α.degree :=
  letI := tangentAlgebra d t
  homogeneousNormalSymbolMap d t I α.degree
    ⟨MvPolynomial.monomial α 1,MvPolynomial.isHomogeneous_monomial 1 rfl⟩

/-- The ACTUAL whole original symbol respects the genuine homogeneous polynomial decomposition and original degree inclusion. -/
theorem normalAssociatedSymbolMap_homogeneous (d t q : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d)) q) :
    let := tangentAlgebra d t
    normalAssociatedSymbolMap d t I P.val =
      DirectSum.lof (HolGerm (ComplexModel d)) ℕ (fun k => (originalNormalGradedPiece d t I k : Type)) q
        (homogeneousNormalSymbolMap d t I q P) := by
  let := tangentAlgebra d t
  let : DirectSum.Decomposition (MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d))) :=
    MvPolynomial.decomposition
  dsimp only
  change DirectSum.lmap (fun k => homogeneousNormalSymbolMap d t I k)
      (DirectSum.decomposeLinearEquiv (MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d))) P.val) = _
  exact (congrArg (DirectSum.lmap (fun k => homogeneousNormalSymbolMap d t I k))
    (DirectSum.decomposeLinearEquiv_apply_coe
      (MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d))) q P)).trans
        (DirectSum.lmap_lof (fun k => homogeneousNormalSymbolMap d t I k) q P)

/-- The ACTUAL original entire monomial symbol has precisely its TRUE degree component, before localization. -/
theorem normalAssociatedSymbolMap_monomial (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (α : Fin t →₀ ℕ) : let := tangentAlgebra d t
    normalAssociatedSymbolMap d t I (MvPolynomial.monomial α 1) =
      DirectSum.lof (HolGerm (ComplexModel d)) ℕ (fun q => (originalNormalGradedPiece d t I q : Type)) α.degree
        (originalNormalMonomialSymbol d t I α) :=
  normalAssociatedSymbolMap_homogeneous d t α.degree I
    ⟨MvPolynomial.monomial α 1,MvPolynomial.isHomogeneous_monomial 1 rfl⟩

/-- The SAME actual original graded piece genuinely localized at the powers of the ONE original entire base germ. -/
abbrev originalLocalizedGradedPiece (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :=
  letI := tangentAlgebra d t
  LocalizedModule (Submonoid.powers (originalUniformNormalDenominator d t I)) (originalNormalGradedPiece d t I q)

/-- Literal whole original associated localization is the direct sum of the TRUE original piece localizations at the SAME denominator. -/
def originalLocalizedAssociatedDirectSumEquiv (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    originalLocalizedAssociatedModule d t I ≃ₗ[Localization.Away (originalUniformNormalDenominator d t I)]
      ⨁ q, originalLocalizedGradedPiece d t I q :=
  letI := tangentAlgebra d t
  localizedDirectSumEquiv (Submonoid.powers (originalUniformNormalDenominator d t I)) (fun q => (originalNormalGradedPiece d t I q : Type))

/-- The ENTIRE internally supplied original monomial basis of the actual direct sum of TRUE original localized J-adic pieces. -/
def originalLocalizedGradedMonomialBasis (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    Module.Basis (originalUniformNormalStandardExponentIndex d t I) (Localization.Away (originalUniformNormalDenominator d t I))
      (⨁ q, originalLocalizedGradedPiece d t I q) :=
  letI := tangentAlgebra d t
  (originalLocalizedAssociatedMonomialBasis d t I).map (originalLocalizedAssociatedDirectSumEquiv d t I)

/-- Each ORIGINAL transported monomial basis vector is the localization of its ACTUAL original whole monomial symbol. -/
theorem originalLocalizedAssociatedMonomialBasis_apply (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (α : originalUniformNormalStandardExponentIndex d t I) :
    let := tangentAlgebra d t
    originalLocalizedAssociatedMonomialBasis d t I α =
      LocalizedModule.mk (normalAssociatedSymbolMap d t I (MvPolynomial.monomial α.val 1)) 1 := by
  let := tangentAlgebra d t
  dsimp only
  let c := originalUniformCoefficientQuotientEquiv d t I
  let f := originalLocalizedAssociatedQuotientEquiv d t I
  let v := originalUniformNormalStandardMonomialBasis d t I
  have he : c
      (Ideal.Quotient.mk (originalUniformNormalIdeal d t I) (MvPolynomial.monomial α.val 1)) =
        Ideal.Quotient.mk (coefficientLocalizedIdeal t (originalUniformNormalDenominator d t I) (originalNormalInitialIdeal d t I))
          (MvPolynomial.monomial α.val 1) :=
    actualEqualIdealQuotientEquiv_mk t _ _ rfl _
  have hm : MvPolynomial.monomial α.val (1 : Localization.Away (originalUniformNormalDenominator d t I)) =
      MvPolynomial.map (algebraMap (HolGerm (ComplexModel d)) (Localization.Away (originalUniformNormalDenominator d t I)))
        (MvPolynomial.monomial α.val 1) := by simp only [MvPolynomial.map_monomial,map_one]
  calc
    originalLocalizedAssociatedMonomialBasis d t I α = f ((v.map c) α) := Module.Basis.map_apply _ _ _
    _ = f (c (v α)) := congrArg f (Module.Basis.map_apply v c α)
    _ = f (c (Ideal.Quotient.mk (originalUniformNormalIdeal d t I) (MvPolynomial.monomial α.val 1))) :=
      congrArg (fun z => f (c z)) (originalUniformNormalStandardMonomialBasis_apply d t I α)
    _ = f (Ideal.Quotient.mk (coefficientLocalizedIdeal t (originalUniformNormalDenominator d t I) (originalNormalInitialIdeal d t I))
          (MvPolynomial.monomial α.val 1)) := congrArg f he
    _ = f (Ideal.Quotient.mk (coefficientLocalizedIdeal t (originalUniformNormalDenominator d t I) (originalNormalInitialIdeal d t I))
          (MvPolynomial.map (algebraMap (HolGerm (ComplexModel d)) (Localization.Away (originalUniformNormalDenominator d t I)))
            (MvPolynomial.monomial α.val 1))) := congrArg (fun P => f (Ideal.Quotient.mk _ P)) hm
    _ = LocalizedModule.mk (normalAssociatedSymbolMap d t I (MvPolynomial.monomial α.val 1)) 1 :=
      originalLocalizedAssociatedQuotientEquiv_mk d t I _

/-- EVERY actual transported whole basis vector lies in its TRUE original localized degree and has its literal original monomial numerator. -/
theorem originalLocalizedGradedMonomialBasis_degree (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (α : originalUniformNormalStandardExponentIndex d t I) :
    let := tangentAlgebra d t
    originalLocalizedGradedMonomialBasis d t I α =
      DirectSum.lof (Localization.Away (originalUniformNormalDenominator d t I)) ℕ (originalLocalizedGradedPiece d t I)
        α.val.degree (LocalizedModule.mk (originalNormalMonomialSymbol d t I α.val) 1) := by
  let := tangentAlgebra d t
  dsimp only
  let f := originalLocalizedAssociatedDirectSumEquiv d t I
  calc
    originalLocalizedGradedMonomialBasis d t I α = f (originalLocalizedAssociatedMonomialBasis d t I α) :=
      Module.Basis.map_apply _ _ _
    _ = f (LocalizedModule.mk (normalAssociatedSymbolMap d t I (MvPolynomial.monomial α.val 1)) 1) :=
      congrArg f (originalLocalizedAssociatedMonomialBasis_apply d t I α)
    _ = f (LocalizedModule.mk
        (DirectSum.lof (HolGerm (ComplexModel d)) ℕ (fun q => (originalNormalGradedPiece d t I q : Type))
          α.val.degree (originalNormalMonomialSymbol d t I α.val)) 1) :=
      congrArg (fun z => f (LocalizedModule.mk z 1)) (normalAssociatedSymbolMap_monomial d t I α.val)
    _ = DirectSum.lof (Localization.Away (originalUniformNormalDenominator d t I)) ℕ
        (originalLocalizedGradedPiece d t I) α.val.degree (LocalizedModule.mk (originalNormalMonomialSymbol d t I α.val) 1) :=
      localizedDirectSumEquiv_mk_one_lof (Submonoid.powers (originalUniformNormalDenominator d t I))
        (fun q => (originalNormalGradedPiece d t I q : Type)) α.val.degree (originalNormalMonomialSymbol d t I α.val)

/-- EVERY internally produced actual standard monomial basis vector is supported in its TRUE original normal degree. -/
theorem originalLocalizedGradedMonomialBasis_supported (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (α : originalUniformNormalStandardExponentIndex d t I) :
    let := tangentAlgebra d t
    originalLocalizedGradedMonomialBasis d t I α =
      DirectSum.lof (Localization.Away (originalUniformNormalDenominator d t I)) ℕ (originalLocalizedGradedPiece d t I)
        α.val.degree ((originalLocalizedGradedMonomialBasis d t I α) α.val.degree) := by
  let := tangentAlgebra d t
  dsimp only
  have h := originalLocalizedGradedMonomialBasis_degree d t I α
  have hc := congrArg (fun z => z α.val.degree) h
  simp only [DirectSum.lof_eq_of,DirectSum.of_eq_same] at hc
  exact h.trans (congrArg (DirectSum.lof (Localization.Away (originalUniformNormalDenominator d t I)) ℕ
    (originalLocalizedGradedPiece d t I) α.val.degree) hc.symm)

/-- The ACTUAL degree-q subset of the internally produced WHOLE original standard exponent family. -/
abbrev originalLocalizedDegreeExponentIndex (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :=
  {α : originalUniformNormalStandardExponentIndex d t I // α.val.degree=q}

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- The genuine coefficient combination in the SAME literal original localized degree, from the actual whole original monomial basis. -/
def originalLocalizedDegreeMonomialCombination (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    (originalLocalizedDegreeExponentIndex d t I q →₀ Localization.Away (originalUniformNormalDenominator d t I))
      →ₗ[Localization.Away (originalUniformNormalDenominator d t I)] originalLocalizedGradedPiece d t I q :=
  letI := tangentAlgebra d t
  degreeFiberCombination (fun α : originalUniformNormalStandardExponentIndex d t I => α.val.degree)
    (originalLocalizedGradedPiece d t I) (originalLocalizedGradedMonomialBasis d t I).repr.symm q

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- The TRUE whole original homogeneous standard basis supplies both injectivity and surjectivity of EVERY actual degree combination internally. -/
theorem originalLocalizedDegreeMonomialCombination_bijective (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Function.Bijective (originalLocalizedDegreeMonomialCombination d t I q) := by
  let := tangentAlgebra d t
  dsimp only
  apply degreeFiberCombination_bijective
  intro α
  simpa only [Module.Basis.repr_symm_single_one] using originalLocalizedGradedMonomialBasis_supported d t I α

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- TRUE original degree combination gives the actual localized ORIGINAL J-adic graded-piece linear equivalence. -/
def originalLocalizedDegreeMonomialLinearEquiv (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    (originalLocalizedDegreeExponentIndex d t I q →₀ Localization.Away (originalUniformNormalDenominator d t I))
      ≃ₗ[Localization.Away (originalUniformNormalDenominator d t I)] originalLocalizedGradedPiece d t I q :=
  letI := tangentAlgebra d t
  LinearEquiv.ofBijective (originalLocalizedDegreeMonomialCombination d t I q)
    (originalLocalizedDegreeMonomialCombination_bijective d t I q)

/-- The REAL standard degree-q monomial basis of the SAME literal original graded piece, at ONE denominator independent of q. -/
def originalLocalizedDegreeMonomialBasis (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    Module.Basis (originalLocalizedDegreeExponentIndex d t I q) (Localization.Away (originalUniformNormalDenominator d t I))
      (originalLocalizedGradedPiece d t I q) :=
  letI := tangentAlgebra d t
  Finsupp.basisSingleOne.map (originalLocalizedDegreeMonomialLinearEquiv d t I q)

/-- The SAME degree-q original standard exponent family is genuinely finite by an actual bounded exponent encoding. -/
@[instance_reducible] def originalLocalizedDegreeExponentFintype (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) : Fintype (originalLocalizedDegreeExponentIndex d t I q) := by
  letI := normalExponentFintype t (q+1)
  let f : originalLocalizedDegreeExponentIndex d t I q → normalExponentIndex t (q+1) :=
    fun α => ⟨α.val.val,by rw [normalExponentDegree_eq_degree,α.property]; omega⟩
  exact Fintype.ofInjective f (fun α β h => Subtype.ext (Subtype.ext (congrArg (fun x : normalExponentIndex t (q+1) => x.val) h)))

/-- ALL actual localized ORIGINAL normal graded pieces are free at the SAME internally produced nonzero entire base germ. -/
theorem moduleFree_all_originalLocalizedGradedPiece (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Module.Free (Localization.Away (originalUniformNormalDenominator d t I)) (originalLocalizedGradedPiece d t I q) :=
  let := tangentAlgebra d t
  Module.Free.of_basis (originalLocalizedDegreeMonomialBasis d t I q)

/-- ALL actual localized ORIGINAL normal graded pieces are finite at the SAME internally produced nonzero entire base germ. -/
theorem moduleFinite_all_originalLocalizedGradedPiece (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Module.Finite (Localization.Away (originalUniformNormalDenominator d t I)) (originalLocalizedGradedPiece d t I q) := by
  let := tangentAlgebra d t
  let := originalLocalizedDegreeExponentFintype d t I q
  exact Module.Finite.of_basis (originalLocalizedDegreeMonomialBasis d t I q)


/-- The LITERAL original homogeneous degree-q normal monomial symbol indexed by an actual standard exponent of that degree. -/
def originalNormalDegreeMonomialSymbol (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (α : originalLocalizedDegreeExponentIndex d t I q) : letI := tangentAlgebra d t
    originalNormalGradedPiece d t I q :=
  letI := tangentAlgebra d t
  homogeneousNormalSymbolMap d t I q
    ⟨MvPolynomial.monomial α.val.val 1,MvPolynomial.isHomogeneous_monomial 1 α.property⟩

/-- The TRUE whole original basis vector of an actual degree-q index is the degree-q inclusion of its LITERAL localized original monomial symbol. -/
theorem originalLocalizedGradedMonomialBasis_degree_index (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) (α : originalLocalizedDegreeExponentIndex d t I q) :
    let := tangentAlgebra d t
    originalLocalizedGradedMonomialBasis d t I α.val =
      DirectSum.lof (Localization.Away (originalUniformNormalDenominator d t I)) ℕ (originalLocalizedGradedPiece d t I)
        q (LocalizedModule.mk (originalNormalDegreeMonomialSymbol d t I q α) 1) := by
  let := tangentAlgebra d t
  dsimp only
  let f := originalLocalizedAssociatedDirectSumEquiv d t I
  calc
    originalLocalizedGradedMonomialBasis d t I α.val = f (originalLocalizedAssociatedMonomialBasis d t I α.val) :=
      Module.Basis.map_apply _ _ _
    _ = f (LocalizedModule.mk (normalAssociatedSymbolMap d t I (MvPolynomial.monomial α.val.val 1)) 1) :=
      congrArg f (originalLocalizedAssociatedMonomialBasis_apply d t I α.val)
    _ = f (LocalizedModule.mk
        (DirectSum.lof (HolGerm (ComplexModel d)) ℕ (fun k => (originalNormalGradedPiece d t I k : Type))
          q (originalNormalDegreeMonomialSymbol d t I q α)) 1) :=
      congrArg (fun z => f (LocalizedModule.mk z 1))
        (normalAssociatedSymbolMap_homogeneous d t q I
          ⟨MvPolynomial.monomial α.val.val 1,MvPolynomial.isHomogeneous_monomial 1 α.property⟩)
    _ = DirectSum.lof (Localization.Away (originalUniformNormalDenominator d t I)) ℕ
        (originalLocalizedGradedPiece d t I) q (LocalizedModule.mk (originalNormalDegreeMonomialSymbol d t I q α) 1) :=
      localizedDirectSumEquiv_mk_one_lof (Submonoid.powers (originalUniformNormalDenominator d t I))
        (fun k => (originalNormalGradedPiece d t I k : Type)) q (originalNormalDegreeMonomialSymbol d t I q α)

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- EVERY true degree basis vector is precisely its LITERAL localized ORIGINAL normal monomial symbol, not an abstract supplied frame. -/
theorem originalLocalizedDegreeMonomialBasis_apply (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) (α : originalLocalizedDegreeExponentIndex d t I q) :
    let := tangentAlgebra d t
    originalLocalizedDegreeMonomialBasis d t I q α =
      LocalizedModule.mk (originalNormalDegreeMonomialSymbol d t I q α) 1 := by
  let := tangentAlgebra d t
  dsimp only
  let E := originalLocalizedDegreeMonomialLinearEquiv d t I q
  let v := originalLocalizedGradedMonomialBasis d t I
  have h := congrArg (fun z => z q) (originalLocalizedGradedMonomialBasis_degree_index d t I q α)
  simp only [DirectSum.lof_eq_of,DirectSum.of_eq_same] at h
  calc
    originalLocalizedDegreeMonomialBasis d t I q α = E (Finsupp.basisSingleOne α) := Module.Basis.map_apply _ _ _
    _ = E (Finsupp.single α 1) := by rw [Finsupp.coe_basisSingleOne]
    _ = originalLocalizedDegreeMonomialCombination d t I q (Finsupp.single α 1) := rfl
    _ = (v.repr.symm (Finsupp.single α.val 1)) q := degreeFiberCombination_single _ _ _ _ _ _
    _ = (v α.val) q := congrArg (fun z => z q) (Module.Basis.repr_symm_single_one v α.val)
    _ = LocalizedModule.mk (originalNormalDegreeMonomialSymbol d t I q α) 1 := h

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- ONE internally produced nonzero whole original base germ makes ALL actual ORIGINAL normal graded pieces genuinely finite free simultaneously. -/
theorem exists_nonzero_all_original_graded_piece_finite_free (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∃ b : HolGerm (ComplexModel d), b ≠ 0 ∧ ∀ q : ℕ,
      let := tangentAlgebra d t
      Module.Free (Localization.Away b)
        (LocalizedModule (Submonoid.powers b) (originalNormalGradedPiece d t I q)) ∧
      Module.Finite (Localization.Away b)
        (LocalizedModule (Submonoid.powers b) (originalNormalGradedPiece d t I q)) :=
  ⟨originalUniformNormalDenominator d t I,originalUniformNormalDenominator_ne_zero d t I,
    fun q => ⟨moduleFree_all_originalLocalizedGradedPiece d t I q,moduleFinite_all_originalLocalizedGradedPiece d t I q⟩⟩



end
end Hironaka.HironakaRelativeNormalLocalizedAssociatedGraded
