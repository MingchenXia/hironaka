/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalGradedAlgebra
import Hironaka.Resolution.HironakaRelativeNormalCoefficientAlgebraNearbyFreeness
import Mathlib.LinearAlgebra.TensorProduct.Basis
/-! # One original-input open for all actual normal degree and truncation ranks

A genuine common coefficient-domain initial ideal has one uniform leading
localization with its literal standard monomial basis. Actual coefficient
base change preserves that same exponent family, even for noninjective nearby
maps. The intrinsic original associated-algebra dictionary retains each basis
vector's true original homogeneous degree, giving fixed finite degree subsets
and exact original normal-layer ranks. Original coherence supplies the whole
coefficient domain, relation ideal, kernel spreading, nearby maps and analytic
nonvanishing open internally. The same open and rank sequence work for every
actual original normal-power truncation by its literal short exact filtration.
Actual origin residue tensor fibres retain those finite dimensions.

This is an original-input uniform-rank producer. The final theorem does not
assume a desired basis, rank, free/flat statement, whole kernel or comparison.
Its open meets every origin neighbourhood; it need not contain the origin.
Identification with the geometric fibre Hilbert--Samuel ideal-power quotient,
smooth-centre sheaf normal flatness, and descent under blowing up are subsequent
producer obligations.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff DirectSum TensorProduct
namespace Hironaka.HironakaRelativeNormalNearbyUniformRanks
noncomputable section

open HironakaRelativeNormalUniformLocalization HironakaRelativeNormalCoefficientPolynomialBaseChange

section BaseChangeNumerators
variable (D T : Type*) [CommRing D] [CommRing T] [Algebra D T]

private theorem polynomialTensorIdeal_image (t : ℕ)
    (H : Ideal (MvPolynomial (Fin t) D)) :
    Ideal.map (MvPolynomial.algebraTensorAlgEquiv (σ := Fin t) D T).toRingHom
      (Ideal.map (Algebra.TensorProduct.includeRight (A := T) (R := D)) H) =
        Ideal.map (MvPolynomial.map (algebraMap D T)) H := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin t) D T
  let J := Ideal.map (Algebra.TensorProduct.includeRight (A := T) (R := D)) H
  have hJ : Ideal.map e.toRingHom J = Ideal.map (MvPolynomial.map (algebraMap D T)) H := by
    dsimp only [J]
    change Ideal.map e.toRingHom
      (Ideal.map (Algebra.TensorProduct.includeRight (A := T) (R := D)).toRingHom H) = _
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro Q
    change e (1 ⊗ₜ[D] Q) = MvPolynomial.map (algebraMap D T) Q
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  exact hJ

/-- Whole coefficient base change using explicit equal-ideal quotient maps. -/
def polynomialQuotientCoefficientAlgEquiv (t : ℕ)
    (H : Ideal (MvPolynomial (Fin t) D)) :
    (T ⊗[D] (MvPolynomial (Fin t) D ⧸ H)) ≃ₐ[T]
      (MvPolynomial (Fin t) T ⧸ Ideal.map (MvPolynomial.map (algebraMap D T)) H) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin t) D T
  let J := Ideal.map (Algebra.TensorProduct.includeRight (A := T) (R := D)) H
  exact ((Algebra.TensorProduct.tensorQuotientEquiv (R := D) T (MvPolynomial (Fin t) D) T H).trans
    (wholeIdealQuotientAlgEquiv e J)).trans
      (Ideal.quotientEquivAlgOfEq T (polynomialTensorIdeal_image D T t H))

/-- Every actual numerator retains the literal whole coefficient-image class. -/
theorem polynomialQuotientCoefficientAlgEquiv_tmul_mk (t : ℕ)
    (H : Ideal (MvPolynomial (Fin t) D)) (P : MvPolynomial (Fin t) D) :
    polynomialQuotientCoefficientAlgEquiv D T t H ((1 : T) ⊗ₜ[D] Ideal.Quotient.mk H P) =
      Ideal.Quotient.mk (Ideal.map (MvPolynomial.map (algebraMap D T)) H)
        (MvPolynomial.map (algebraMap D T) P) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin t) D T
  let J := Ideal.map (Algebra.TensorProduct.includeRight (A := T) (R := D)) H
  unfold polynomialQuotientCoefficientAlgEquiv
  change Ideal.quotientEquivAlgOfEq T (I := Ideal.map e.toRingHom J)
      (J := Ideal.map (MvPolynomial.map (algebraMap D T)) H) (polynomialTensorIdeal_image D T t H)
    (Ideal.Quotient.mk (Ideal.map e.toRingHom J) (e ((1 : T) ⊗ₜ[D] P))) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

end BaseChangeNumerators

section UniformImages
variable {D K T : Type*} [CommRing D] [IsDomain D] [Field K]
  [Algebra D K] [IsFractionRing D K] [CommRing T]

private theorem coefficientUniformImageIdeal_eq
    (t : ℕ) (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* T) (hf : IsUnit (f (uniformLeadingDenominator (K := K) t m H))) :
    let := (IsLocalization.Away.lift (S := Localization.Away (uniformLeadingDenominator (K := K) t m H)) (uniformLeadingDenominator (K := K) t m H) hf).toAlgebra
    Ideal.map (MvPolynomial.map
      (algebraMap (Localization.Away (uniformLeadingDenominator (K := K) t m H)) T))
        (uniformLocalizedIdeal (K := K) t m H) = Ideal.map (MvPolynomial.map f) H := by
  let b := uniformLeadingDenominator (K := K) t m H
  let L := Localization.Away b
  let f' : L →+* T := IsLocalization.Away.lift (S := Localization.Away b) b hf
  let := f'.toAlgebra
  have hcomp : f'.comp (algebraMap D L) = f := by
    apply RingHom.ext
    intro r
    exact IsLocalization.Away.lift_eq b hf r
  change Ideal.map (MvPolynomial.map f')
    (Ideal.map (MvPolynomial.map (algebraMap D L)) H) = _
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro P
  change MvPolynomial.map f' (MvPolynomial.map (algebraMap D L) P) = MvPolynomial.map f P
  rw [MvPolynomial.map_map, hcomp]

/-- The literal coefficient-image quotient is the genuine base change from the one original localization. -/
def coefficientImageBaseChangeEquiv
    (t : ℕ) (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* T) (hf : IsUnit (f (uniformLeadingDenominator (K := K) t m H))) :
    letI := (IsLocalization.Away.lift (S := Localization.Away (uniformLeadingDenominator (K := K) t m H)) (uniformLeadingDenominator (K := K) t m H) hf).toAlgebra
    (T ⊗[Localization.Away (uniformLeadingDenominator (K := K) t m H)]
      (MvPolynomial (Fin t) (Localization.Away (uniformLeadingDenominator (K := K) t m H)) ⧸
        uniformLocalizedIdeal (K := K) t m H)) ≃ₐ[T]
          (MvPolynomial (Fin t) T ⧸ Ideal.map (MvPolynomial.map f) H) := by
  let b := uniformLeadingDenominator (K := K) t m H
  let L := Localization.Away b
  letI := (IsLocalization.Away.lift (S := Localization.Away b) b hf).toAlgebra
  exact (polynomialQuotientCoefficientAlgEquiv L T t (uniformLocalizedIdeal (K := K) t m H)).trans
    (Ideal.quotientEquivAlgOfEq T (coefficientUniformImageIdeal_eq (K := K) t m H f hf))

theorem coefficientImageBaseChangeEquiv_tmul_mk
    (t : ℕ) (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* T) (hf : IsUnit (f (uniformLeadingDenominator (K := K) t m H)))
    (P : MvPolynomial (Fin t) (Localization.Away (uniformLeadingDenominator (K := K) t m H))) :
    let := (IsLocalization.Away.lift (S := Localization.Away (uniformLeadingDenominator (K := K) t m H)) (uniformLeadingDenominator (K := K) t m H) hf).toAlgebra
    coefficientImageBaseChangeEquiv (K := K) t m H f hf
      ((1 : T) ⊗ₜ[Localization.Away (uniformLeadingDenominator (K := K) t m H)]
        Ideal.Quotient.mk (uniformLocalizedIdeal (K := K) t m H) P) =
      Ideal.Quotient.mk (Ideal.map (MvPolynomial.map f) H)
        (MvPolynomial.map (IsLocalization.Away.lift (S := Localization.Away (uniformLeadingDenominator (K := K) t m H)) (uniformLeadingDenominator (K := K) t m H) hf) P) := by
  let b := uniformLeadingDenominator (K := K) t m H
  let L := Localization.Away b
  let := (IsLocalization.Away.lift (S := Localization.Away b) b hf).toAlgebra
  unfold coefficientImageBaseChangeEquiv
  rw [AlgEquiv.trans_apply, polynomialQuotientCoefficientAlgEquiv_tmul_mk,
    Ideal.quotientEquivAlgOfEq_mk]
  rfl

/-- A single genuine original exponent family bases every actual coefficient-image whole quotient. -/
def coefficientImageStandardMonomialBasis
    (t : ℕ) (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* T) (hf : IsUnit (f (uniformLeadingDenominator (K := K) t m H))) :
    Module.Basis (uniformStandardExponentIndex (K := K) t m H) T
      (MvPolynomial (Fin t) T ⧸ Ideal.map (MvPolynomial.map f) H) :=
  letI := (IsLocalization.Away.lift (S := Localization.Away (uniformLeadingDenominator (K := K) t m H)) (uniformLeadingDenominator (K := K) t m H) hf).toAlgebra
  ((uniformStandardMonomialBasis (K := K) t m H).baseChange T).map
    (coefficientImageBaseChangeEquiv (K := K) t m H f hf).toLinearEquiv

theorem coefficientImageStandardMonomialBasis_apply
    (t : ℕ) (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* T) (hf : IsUnit (f (uniformLeadingDenominator (K := K) t m H)))
    (α : uniformStandardExponentIndex (K := K) t m H) :
    coefficientImageStandardMonomialBasis (K := K) t m H f hf α =
      Ideal.Quotient.mk (Ideal.map (MvPolynomial.map f) H) (MvPolynomial.monomial α.val (1 : T)) := by
  let b := uniformLeadingDenominator (K := K) t m H
  let := (IsLocalization.Away.lift (S := Localization.Away b) b hf).toAlgebra
  rw [coefficientImageStandardMonomialBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    uniformStandardMonomialBasis_apply]
  change coefficientImageBaseChangeEquiv (K := K) t m H f hf
    ((1 : T) ⊗ₜ[Localization.Away b] Ideal.Quotient.mk (uniformLocalizedIdeal (K := K) t m H)
      (MvPolynomial.monomial α.val (1 : Localization.Away b))) = _
  rw [coefficientImageBaseChangeEquiv_tmul_mk, MvPolynomial.map_monomial, map_one]

end UniformImages

section HomogeneousBasis
variable {B : Type*} [CommRing B]

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

/-- A whole homogeneous basis internally restricts to an actual degree-fibre isomorphism. -/
def homogeneousBasisDegreeLinearEquiv {ι : Type*} (ν : ι → ℕ) (M : ℕ → Type*)
    [∀ q, AddCommGroup (M q)] [∀ q, Module B (M q)]
    (e : (ι →₀ B) ≃ₗ[B] ⨁ q, M q)
    (hgrade : ∀ i, e (Finsupp.single i 1) = DirectSum.lof B ℕ M (ν i) (e (Finsupp.single i 1) (ν i)))
    (q : ℕ) : ({i : ι // ν i=q} →₀ B) ≃ₗ[B] M q :=
  LinearEquiv.ofBijective (degreeFiberCombination ν M e q)
    (degreeFiberCombination_bijective ν M e hgrade q)

end HomogeneousBasis

open HironakaRelativeNormalMonomialBasis HironakaRelativeNormalAssociatedGraded

abbrev uniformDegreeStandardExponentIndex {D K : Type*} [CommRing D] [IsDomain D] [Field K]
    [Algebra D K] [IsFractionRing D K] (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) D)) (q : ℕ) :=
  {α : uniformStandardExponentIndex (K := K) t m H // α.val.degree=q}

@[instance_reducible] def uniformDegreeStandardExponentFintype
    {D K : Type*} [CommRing D] [IsDomain D] [Field K] [Algebra D K] [IsFractionRing D K]
    (t : ℕ) (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D)) (q : ℕ) :
    Fintype (uniformDegreeStandardExponentIndex (K := K) t m H q) := by
  letI := normalExponentFintype t (q+1)
  let f : uniformDegreeStandardExponentIndex (K := K) t m H q → normalExponentIndex t (q+1) :=
    fun α => ⟨α.val.val, by rw [normalExponentDegree_eq_degree, α.property]; omega⟩
  exact Fintype.ofInjective f (fun α β h =>
    Subtype.ext (Subtype.ext (congrArg (fun x : normalExponentIndex t (q+1) => x.val) h)))

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalLocalizedAssociatedGraded HironakaRelativeNormalGradedAlgebra

attribute [local instance] originalNormalAssociatedGradedCommRing originalNormalAssociatedGradedAlgebra

section OriginalBasis
variable {D K : Type*} [CommRing D] [IsDomain D] [Field K]
  [Algebra D K] [IsFractionRing D K]

/-- Actual coefficient-image monomials in the intrinsic original associated algebra. -/
def originalCoefficientImageMonomialBasis (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* HolGerm (ComplexModel d))
    (hf : IsUnit (f (uniformLeadingDenominator (K := K) t m H)))
    (hH : Ideal.map (MvPolynomial.map f) H = originalNormalInitialIdeal d t I) :
    letI := tangentAlgebra d t
    Module.Basis (uniformStandardExponentIndex (K := K) t m H) (HolGerm (ComplexModel d))
      (originalNormalAssociatedGraded d t I) :=
  letI := tangentAlgebra d t
  (coefficientImageStandardMonomialBasis (K := K) t m H f hf).map
    ((Ideal.quotientEquivAlgOfEq (HolGerm (ComplexModel d)) hH).trans
      (originalNormalAssociatedGradedQuotientAlgEquiv d t I)).toLinearEquiv

/-- Every transported whole basis vector is precisely the unchanged original monomial symbol. -/
theorem originalCoefficientImageMonomialBasis_apply (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* HolGerm (ComplexModel d))
    (hf : IsUnit (f (uniformLeadingDenominator (K := K) t m H)))
    (hH : Ideal.map (MvPolynomial.map f) H = originalNormalInitialIdeal d t I)
    (α : uniformStandardExponentIndex (K := K) t m H) :
    let := tangentAlgebra d t
    originalCoefficientImageMonomialBasis d t I m H f hf hH α =
      normalAssociatedSymbolMap d t I (MvPolynomial.monomial α.val 1) := by
  let := tangentAlgebra d t
  dsimp only
  change ((Ideal.quotientEquivAlgOfEq (HolGerm (ComplexModel d)) hH).trans
    (originalNormalAssociatedGradedQuotientAlgEquiv d t I))
      (coefficientImageStandardMonomialBasis (K := K) t m H f hf α) = _
  rw [coefficientImageStandardMonomialBasis_apply]
  change originalNormalAssociatedGradedQuotientAlgEquiv d t I
    ((Ideal.quotientEquivAlgOfEq (HolGerm (ComplexModel d)) hH)
      (Ideal.Quotient.mk (Ideal.map (MvPolynomial.map f) H) (MvPolynomial.monomial α.val 1))) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, originalNormalAssociatedGradedQuotientAlgEquiv_mk]

private theorem originalCoefficientImageMonomialBasis_supported (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* HolGerm (ComplexModel d))
    (hf : IsUnit (f (uniformLeadingDenominator (K := K) t m H)))
    (hH : Ideal.map (MvPolynomial.map f) H = originalNormalInitialIdeal d t I)
    (α : uniformStandardExponentIndex (K := K) t m H) :
    let := tangentAlgebra d t
    originalCoefficientImageMonomialBasis d t I m H f hf hH α =
      DirectSum.lof (HolGerm (ComplexModel d)) ℕ (fun q => (originalNormalGradedPiece d t I q : Type))
        α.val.degree ((originalCoefficientImageMonomialBasis d t I m H f hf hH α) α.val.degree) := by
  let := tangentAlgebra d t
  have h := (originalCoefficientImageMonomialBasis_apply d t I m H f hf hH α).trans
    (normalAssociatedSymbolMap_monomial d t I α.val)
  have hc := congrArg (fun z => z α.val.degree) h
  simp only [DirectSum.lof_eq_of, DirectSum.of_eq_same] at hc
  exact h.trans (congrArg (DirectSum.lof (HolGerm (ComplexModel d)) ℕ
    (fun q => (originalNormalGradedPiece d t I q : Type)) α.val.degree) hc.symm)

/-- The actual fixed standard exponent degree fibre bases each original normal layer. -/
def originalDegreeCoefficientImageMonomialBasis (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* HolGerm (ComplexModel d))
    (hf : IsUnit (f (uniformLeadingDenominator (K := K) t m H)))
    (hH : Ideal.map (MvPolynomial.map f) H = originalNormalInitialIdeal d t I) (q : ℕ) :
    letI := tangentAlgebra d t
    Module.Basis (uniformDegreeStandardExponentIndex (K := K) t m H q)
      (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) := by
  letI := tangentAlgebra d t
  let v := originalCoefficientImageMonomialBasis d t I m H f hf hH
  exact Finsupp.basisSingleOne.map
    (homogeneousBasisDegreeLinearEquiv (fun α : uniformStandardExponentIndex (K := K) t m H => α.val.degree)
      (fun q => (originalNormalGradedPiece d t I q : Type)) v.repr.symm
      (fun α => by simpa only [Module.Basis.repr_symm_single_one] using
        originalCoefficientImageMonomialBasis_supported d t I m H f hf hH α) q)

/-- The rank is the fixed finite standard-degree cardinal, independently of the nearby coefficient homomorphism. -/
theorem originalDegreeCoefficientImageMonomialBasis_finrank (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* HolGerm (ComplexModel d))
    (hf : IsUnit (f (uniformLeadingDenominator (K := K) t m H)))
    (hH : Ideal.map (MvPolynomial.map f) H = originalNormalInitialIdeal d t I) (q : ℕ) :
    let := tangentAlgebra d t
    Module.finrank (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) =
      Nat.card (uniformDegreeStandardExponentIndex (K := K) t m H q) := by
  let := tangentAlgebra d t
  exact Module.finrank_eq_nat_card_basis (originalDegreeCoefficientImageMonomialBasis d t I m H f hf hH q)

end OriginalBasis

open OkaRelationSheaf HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalCoefficientFunctionAlgebra
  HironakaRelativeNormalCoefficientAlgebraNearbyFreeness HironakaRelativeNormalUniformTruncations

attribute [local instance] coefficientSubalgebraRing

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- Original coherence internally supplies one analytic open and one whole original degree-rank sequence. -/
theorem exists_original_nearby_all_degree_uniform_rank_open (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ U : Set (ComplexModel d), ∃ r : ℕ → ℕ, IsOpen U ∧
      (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
      ∀ a ∈ U, ∀ q : ℕ,
        Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) ∧
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) ∧
        Module.finrank (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) = r q := by
  classical
  let := tangentAlgebra d t
  obtain ⟨B, _hB, h0, C, _hC, hD, _hDf, W, hW, h0W, hWB, ρ, Q, _hhom, hρ, hideal⟩ :=
    exists_original_common_domain_coefficient_initial_family d t I hI
  let D := coefficientOriginAlgebra d B h0 C
  let : IsDomain D := hD
  let : Field (FractionRing D) := FractionRing.field D
  let H : Ideal (MvPolynomial (Fin t) D) := Ideal.span (range Q)
  let b := uniformLeadingDenominator (K := FractionRing D) t (MonomialOrder.degLex (σ := Fin t)) H
  have hb : b ≠ 0 := uniformLeadingDenominator_ne_zero _ _ _
  obtain ⟨c, hcb⟩ := Ideal.Quotient.mk_surjective b
  let g : ComplexModel d → ℂ := (C.val c).val
  have hc0 : ((coefficientGermHom d B 0 h0).comp C.val) c ≠ 0 := by
    intro hz
    have hc : c ∈ coefficientOriginKernel d B h0 C := hz
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr hc
    rw [hcb] at he
    exact hb he
  have hg0 : (g : Germ (𝓝 (0 : ComplexModel d)) ℂ) ≠ 0 := by
    intro hz
    apply hc0
    apply Subtype.ext
    change (Germ.coeRingHom (𝓝 (0 : ComplexModel d))) (g ∘ actualAffineTranslation d 0) = 0
    have hid : g ∘ actualAffineTranslation d 0 = g := by
      funext z
      simp only [Function.comp_apply, actualAffineTranslation, zero_add]
    rw [hid]
    exact hz
  let U := {a : ComplexModel d | a ∈ W ∧ g a ≠ 0}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    have hcont : ContinuousAt g a := ((C.val c).property a (hWB ha.1)).self_of_nhds.continuousAt
    filter_upwards [hW.mem_nhds ha.1, hcont.eventually_ne ha.2] with z hz hgz
    exact ⟨hz, hgz⟩
  have hmeet : ∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty := by
    intro V hV
    by_contra hn
    apply hg0
    apply Germ.coe_eq.mpr
    filter_upwards [hV, hW.mem_nhds h0W] with a haV haW
    by_contra hga
    exact hn ⟨a, haV, haW, hga⟩
  let r : ℕ → ℕ := fun q => Nat.card
    (uniformDegreeStandardExponentIndex (K := FractionRing D) t
      (MonomialOrder.degLex (σ := Fin t)) H q)
  refine ⟨U, r, hU, hmeet, ?_⟩
  intro a ha q
  have hvalue : (ρ a ha.1) b = coefficientGermHom d B a (hWB ha.1) (C.val c) := by
    rw [← hcb]
    exact congrArg (fun f : C →ₐ[ℂ] HolGerm (ComplexModel d) => f c) (hρ a ha.1)
  have hunit : IsUnit ((ρ a ha.1) b) := by
    apply (HolGerm.isUnit_iff_eval_ne_zero ((ρ a ha.1) b)).mpr
    rw [hvalue]
    change g (actualAffineTranslation d a 0) ≠ 0
    simpa only [actualAffineTranslation_zero] using ha.2
  have hH : Ideal.map (MvPolynomial.map (ρ a ha.1).toRingHom) H =
      originalNormalInitialIdeal d t
        (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) :=
    hideal a ha.1
  let := uniformDegreeStandardExponentFintype (K := FractionRing D) t
    (MonomialOrder.degLex (σ := Fin t)) H q
  let bv := originalDegreeCoefficientImageMonomialBasis
    (K := FractionRing D) d t
    (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a)))
    (MonomialOrder.degLex (σ := Fin t)) H (ρ a ha.1).toRingHom hunit hH q
  exact ⟨Module.Free.of_basis bv, Module.Finite.of_basis bv, Module.finrank_eq_nat_card_basis bv⟩

private theorem actual_short_exact_middle_finrank {R L M N : Type} [CommRing R]
    [StrongRankCondition R] [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N] [Module.Free R L] [Module.Free R N]
    [Module.Finite R L] [Module.Finite R N]
    (g : L →ₗ[R] M) (h : M →ₗ[R] N) (hg : Function.Injective g)
    (hh : Function.Surjective h) (ex : Function.Exact g h) :
    Module.finrank R M = Module.finrank R L + Module.finrank R N := by
  let S := ModuleCat.shortComplexOfCompEqZero g h ex.linearMap_comp_eq_zero
  have hs := ModuleCat.shortComplex_shortExact S ex hg hh
  exact ModuleCat.free_shortExact_finrank_add hs rfl rfl

/-- Actual finite free degree ranks determine every literal original truncation rank. -/
theorem all_originalNormalTruncation_finrank_of_graded (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (r : ℕ → ℕ) :
    let := tangentAlgebra d t
    (∀ q : ℕ, Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) ∧
      Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) ∧
      Module.finrank (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) = r q) →
    ∀ q : ℕ, Module.finrank (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q) =
      ∑ i ∈ Finset.range q, r i := by
  let := tangentAlgebra d t
  dsimp only
  intro hdegree
  have hff := all_originalNormalTruncation_finite_free_of_graded_free d t I
    (fun q => ⟨(hdegree q).1, (hdegree q).2.1⟩)
  intro q
  induction q with
  | zero =>
    let := originalNormalTruncation_zero_subsingleton d t I
    have hb := Module.finrank_eq_nat_card_basis
      (Module.Basis.empty _ :
        Module.Basis PEmpty.{1} (HolGerm (ComplexModel d)) (originalNormalTruncation d t I 0))
    simpa using hb
  | succ q ih =>
    let := (hff q).1
    let := (hff q).2
    let := (hdegree q).1
    let := (hdegree q).2.1
    have hr := actual_short_exact_middle_finrank
      (originalNormalTruncationPieceInclusion d t I q)
      (originalNormalTruncationMap d t I q).toLinearMap
      (originalNormalTruncationPieceInclusion_injective d t I q)
      (originalNormalTruncationMap_surjective d t I q) (originalNormalTruncation_exact d t I q)
    rw [hr, (hdegree q).2.2, ih, Finset.sum_range_succ]
    exact Nat.add_comm _ _

/-- Original coherence supplies one rank sequence for all actual original degrees and full truncations on one open. -/
theorem exists_original_nearby_all_truncation_uniform_rank_open (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ U : Set (ComplexModel d), ∃ r : ℕ → ℕ, IsOpen U ∧
      (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
      (∀ a ∈ U, ∀ q : ℕ,
        Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) ∧
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) ∧
        Module.finrank (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) = r q) ∧
      (∀ a ∈ U, ∀ q : ℕ,
        Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) ∧
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) ∧
        Module.finrank (HolGerm (ComplexModel d)) (originalNormalTruncation d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) =
            ∑ i ∈ Finset.range q, r i) := by
  let := tangentAlgebra d t
  obtain ⟨U, r, hU, hmeet, hdegree⟩ := exists_original_nearby_all_degree_uniform_rank_open d t I hI
  refine ⟨U, r, hU, hmeet, hdegree, ?_⟩
  intro a ha q
  have hff := all_originalNormalTruncation_finite_free_of_graded_free d t _
    (fun k => ⟨(hdegree a ha k).1, (hdegree a ha k).2.1⟩) q
  exact ⟨hff.1, hff.2, all_originalNormalTruncation_finrank_of_graded d t _ r (hdegree a ha) q⟩

/-- The actual origin residue algebra on complex coefficients, given by genuine base-germ evaluation. -/
@[instance_reducible] def baseGermResidueAlgebra (d : ℕ) :
    Algebra (HolGerm (ComplexModel d)) ℂ :=
  (HolGerm.eval : HolGerm (ComplexModel d) →+* ℂ).toAlgebra

attribute [local instance] baseGermResidueAlgebra

/-- The complex dimension of a genuine original residue tensor fibre is the actual free base rank. -/
theorem originalNormalFibreTruncation_finrank (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q) →
      Module.finrank ℂ (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t I q) =
        Module.finrank (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q) := by
  let := tangentAlgebra d t
  dsimp only
  intro hfree
  let := hfree
  exact Module.finrank_baseChange (R := ℂ) (S := HolGerm (ComplexModel d))
    (M' := originalNormalTruncation d t I q)

/-- One original-input open supplies the full actual degree/truncation ranks and every algebraic fibre dimension. -/
theorem exists_original_nearby_all_fibre_truncation_dimension_open (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ U : Set (ComplexModel d), ∃ r : ℕ → ℕ, IsOpen U ∧
      (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
      (∀ a ∈ U, ∀ q : ℕ,
        Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) ∧
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) ∧
        Module.finrank (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) = r q) ∧
      (∀ a ∈ U, ∀ q : ℕ,
        Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) ∧
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) ∧
        Module.finrank (HolGerm (ComplexModel d)) (originalNormalTruncation d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) =
            ∑ i ∈ Finset.range q, r i) ∧
      (∀ a ∈ U, ∀ q : ℕ,
        Module.Finite ℂ (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) ∧
        Module.finrank ℂ (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) q) =
            ∑ i ∈ Finset.range q, r i) := by
  let := tangentAlgebra d t
  obtain ⟨U, r, hU, hmeet, hdegree, htrunc⟩ :=
    exists_original_nearby_all_truncation_uniform_rank_open d t I hI
  refine ⟨U, r, hU, hmeet, hdegree, htrunc, ?_⟩
  intro a ha q
  let := (htrunc a ha q).1
  let := (htrunc a ha q).2.1
  exact ⟨inferInstance, (originalNormalFibreTruncation_finrank d t _ q (htrunc a ha q).1).trans
    (htrunc a ha q).2.2⟩

end
end Hironaka.HironakaRelativeNormalNearbyUniformRanks
