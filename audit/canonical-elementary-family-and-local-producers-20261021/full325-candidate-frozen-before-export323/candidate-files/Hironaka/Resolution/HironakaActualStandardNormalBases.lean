/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualBaseResidueField
import Hironaka.Resolution.HironakaActualFormalStandardMonomialHS
import Hironaka.Resolution.HironakaActualTangentCutLayers
import Hironaka.Resolution.HironakaActualRelativeTaylorCoefficients
import Mathlib.RingTheory.LocalRing.Module
/-!
# Literal standard normal monomials over the original centre base

The actual whole complex fibre dictionary and genuine formal point-jet
standard monomials construct a literal complex residue basis. The canonical
local residue field and Nakayama lift those prescribed analytic monomials,
when the actual normal truncation is finite free. Every standard exponent
has zero tangent block, so the resulting basis consists of actual normal
coordinate monomials. Original constant-HS regular-centre geometry internally
produces all required truncation freeness for one unchanged origin ideal.

The index uses the genuine fibre ideal's diagram. Comparing it with the
original ideal's diagram and proving whole reduced-vertex normal support
remain separate assertions; this module does not claim Bennett or general G8.
-/

set_option autoImplicit false
open scoped TensorProduct
open TensorProduct
namespace Hironaka.HironakaActualStandardNormalBases
noncomputable section
open HolGerm HironakaActualBaseResidueField
attribute [local instance] HironakaRelativeNormalNearbyUniformRanks.baseGermResidueAlgebra
variable (d : ℕ) {Q ι : Type*} [AddCommGroup Q] [Module (HolGerm (ComplexModel d)) Q]
  [Module.FinitePresentation (HolGerm (ComplexModel d)) Q] [Module.Flat (HolGerm (ComplexModel d)) Q]
theorem exists_basis_of_complex_basis (v : ι → Q)
    (bC : Module.Basis ι ℂ (ℂ ⊗[HolGerm (ComplexModel d)] Q))
    (hbC : ∀ i, bC i = (1 : ℂ) ⊗ₜ[HolGerm (ComplexModel d)] v i) :
    ∃ b : Module.Basis ι (HolGerm (ComplexModel d)) Q, ∀ i, b i=v i := by
  let B := HolGerm (ComplexModel d)
  let k := IsLocalRing.ResidueField B
  let e := baseResidueFieldEquiv d
  let : Algebra k ℂ := e.toRingHom.toAlgebra
  let E : (k ⊗[B] Q) ≃ₗ[k] (ℂ ⊗[B] Q) :=
    { (residueTensorEquiv d Q).toAddEquiv with
      map_smul' := by
        intro a z
        change residueTensorEquiv d Q (a • z) = a • residueTensorEquiv d Q z
        induction z using TensorProduct.induction_on with
        | zero => simp only [smul_zero,map_zero]
        | tmul b x =>
          change e (a*b) ⊗ₜ[B] x = (e a*e b) ⊗ₜ[B] x
          rw [map_mul]
        | add z w hz hw => simpa only [smul_add,map_add] using congrArg₂ (·+·) hz hw }
  let bkC : Module.Basis ι k (ℂ ⊗[B] Q) :=
    bC.mapCoeffs e.symm.toRingEquiv (fun c x => by
      change e (e.symm c) • x = c • x
      rw [AlgEquiv.apply_symm_apply])
  let bk := bkC.map E.symm
  have hbk : ∀ i, bk i = (1 : k) ⊗ₜ[B] v i := by
    intro i
    apply E.injective
    rw [Module.Basis.map_apply,LinearEquiv.apply_symm_apply,Module.Basis.mapCoeffs_apply,hbC]
    change (1 : ℂ) ⊗ₜ[B] v i = e 1 ⊗ₜ[B] v i
    rw [map_one]
  have hfun : (TensorProduct.mk B k Q 1 ∘ v) = (bk : ι → k ⊗[B] Q) := by
    funext i
    exact (hbk i).symm
  apply Module.exists_basis_of_basis_baseChange v
  · rw [hfun]
    exact bk.linearIndependent
  · rw [hfun]
    exact bk.span_eq
  · exact Module.Flat.rTensor_preserves_injective_linearMap
      (IsLocalRing.maximalIdeal B).subtype Subtype.val_injective

section Fibre
open HironakaRelativeNormalIdeal HironakaRelativeNormalUniformTruncations
  HironakaRelativeNormalFibreHilbertSamuel HironakaActualOriginalFormalHSTransfer
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalStandardMonomialHS
  HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalMonomialBasis
variable (t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t

private theorem exists_unshiftedWholeJetEquiv (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (q : ℕ) :
    ∃ e : (HolGerm (ComplexModel n) ⧸
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q)) ≃ₐ[ℂ]
      (MvPowerSeries (Fin n) ℂ ⧸
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I ⊔ genuineFormalVariables n^q)),
      ∀ g, e (Ideal.Quotient.mk _ g) = Ideal.Quotient.mk _ (actualUnshiftedTaylorAlgHom n g) := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ J : Ideal (HolGerm (ComplexModel m)), ∃ e :
      (HolGerm (ComplexModel m) ⧸ (J ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel m))^q)) ≃ₐ[ℂ]
      (MvPowerSeries (Fin n) ℂ ⧸ (Ideal.map f.toRingHom J ⊔ genuineFormalVariables n^q)),
      ∀ g, e (Ideal.Quotient.mk _ g) = Ideal.Quotient.mk _ (f g)
  have h : P (0+n) (HironakaActualOriginalFormalTaylor.originalTaylorAlgHom n) := by
    intro J
    exact ⟨originalFormalWholeJetAlgEquiv n J q, fun _ => rfl⟩
  have hc (m : ℕ) (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (0+n) (Nat.zero_add n) _ h I

def unshiftedWholeJetEquiv (n : ℕ) (I : Ideal (HolGerm (ComplexModel n))) (q : ℕ) :=
  Classical.choose (exists_unshiftedWholeJetEquiv n I q)

theorem unshiftedWholeJetEquiv_mk (n : ℕ) (I : Ideal (HolGerm (ComplexModel n))) (q : ℕ)
    (g : HolGerm (ComplexModel n)) :
    unshiftedWholeJetEquiv n I q (Ideal.Quotient.mk _ g) =
      Ideal.Quotient.mk _ (actualUnshiftedTaylorAlgHom n g) :=
  Classical.choose_spec (exists_unshiftedWholeJetEquiv n I q) g

def fibreFormalIdeal (I : Ideal (HolGerm (ComplexModel (d+t)))) : Ideal (MvPowerSeries (Fin (d+t)) ℂ) :=
  Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (I ⊔ originalBaseMaximalIdeal d t)

def normalFibreFormalJetEquiv (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t I q) ≃ₐ[ℂ]
      (MvPowerSeries (Fin (d+t)) ℂ ⧸ (fibreFormalIdeal d t I ⊔ genuineFormalVariables (d+t)^q)) :=
  ((originalNormalFibreTruncationAlgEquiv d t I q).trans
    (Ideal.quotientEquivAlgOfEq ℂ (fibreMaximalIdeal_power_eq d t q I).symm)).trans
      (unshiftedWholeJetEquiv (d+t) (I ⊔ originalBaseMaximalIdeal d t) q)

theorem normalFibreFormalJetEquiv_tmul_mk (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (c : ℂ) (g : HolGerm (ComplexModel (d+t))) :
    normalFibreFormalJetEquiv d t I q (c ⊗ₜ[HolGerm (ComplexModel d)] Ideal.Quotient.mk _ g) =
      c • Ideal.Quotient.mk _ (actualUnshiftedTaylorAlgHom (d+t) g) := by
  change unshiftedWholeJetEquiv (d+t) (I ⊔ originalBaseMaximalIdeal d t) q
    (Ideal.quotientEquivAlgOfEq ℂ (fibreMaximalIdeal_power_eq d t q I).symm
      (originalNormalFibreTruncationAlgEquiv d t I q (c ⊗ₜ[HolGerm (ComplexModel d)] Ideal.Quotient.mk _ g))) = _
  rw [originalNormalFibreTruncationAlgEquiv_tmul_mk,map_smul,map_smul]
  change c • unshiftedWholeJetEquiv (d+t) (I ⊔ originalBaseMaximalIdeal d t) q
    (Ideal.Quotient.mk _ g) = _
  rw [unshiftedWholeJetEquiv_mk]
  rfl

def analyticMonomial (n : ℕ) (α : Fin n →₀ ℕ) : HolGerm (ComplexModel n) :=
  ∏ i, coordinateGerm i ^ α i

theorem actualTaylor_analyticMonomial (n : ℕ) (α : Fin n →₀ ℕ) :
    actualUnshiftedTaylorAlgHom n (analyticMonomial n α) = MvPowerSeries.monomial α (1 : ℂ) := by
  rw [analyticMonomial,map_prod]
  simp_rw [map_pow,actualUnshiftedTaylor_coordinate]
  symm
  rw [MvPowerSeries.monomial_one_eq]
  exact α.prod_fintype (fun i k => (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ)^k) (fun _ => pow_zero _)

def complexStandardMonomialBasis (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    Module.Basis (actualStandardIndex (d+t) (fibreFormalIdeal d t I) q) ℂ
      (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t I q) :=
  ((Pi.basisFun ℂ (actualStandardIndex (d+t) (fibreFormalIdeal d t I) q)).map
    (actualStandardQuotientLinearEquiv (d+t) (fibreFormalIdeal d t I) q)).map
      (normalFibreFormalJetEquiv d t I q).symm.toLinearEquiv

theorem complexStandardMonomialBasis_apply (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (α : actualStandardIndex (d+t) (fibreFormalIdeal d t I) q) :
    complexStandardMonomialBasis d t I q α =
      (1 : ℂ) ⊗ₜ[HolGerm (ComplexModel d)]
        Ideal.Quotient.mk (I ⊔ normalIdeal d t^q) (analyticMonomial (d+t) α.val.val) := by
  apply (normalFibreFormalJetEquiv d t I q).injective
  rw [normalFibreFormalJetEquiv_tmul_mk,one_smul,actualTaylor_analyticMonomial]
  rw [complexStandardMonomialBasis,Module.Basis.map_apply,Module.Basis.map_apply]
  change normalFibreFormalJetEquiv d t I q
    ((normalFibreFormalJetEquiv d t I q).symm
      (actualStandardQuotientLinearEquiv (d+t) (fibreFormalIdeal d t I) q
        (Pi.basisFun ℂ (actualStandardIndex (d+t) (fibreFormalIdeal d t I) q) α))) = _
  rw [AlgEquiv.apply_symm_apply,Pi.basisFun_apply]
  change actualStandardQuotientMap (d+t) (fibreFormalIdeal d t I) q (Pi.single α 1)=_
  rw [actualStandardQuotientMap_apply]
  apply congrArg (Ideal.Quotient.mk _)
  change (∑ a : actualStandardIndex (d+t) (fibreFormalIdeal d t I) q,
    MvPowerSeries.monomial a.val.val (Pi.single α 1 a)) = _
  rw [Finset.sum_eq_single α]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb,map_zero]
  · intro hα
    exact False.elim (hα (Finset.mem_univ α))


theorem exists_standardMonomialBasis (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    [Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q)]
    [Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q)] :
    ∃ b : Module.Basis (actualStandardIndex (d+t) (fibreFormalIdeal d t I) q)
      (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q),
      ∀ α, b α = Ideal.Quotient.mk (I ⊔ normalIdeal d t^q) (analyticMonomial (d+t) α.val.val) := by
  let : Module.FinitePresentation (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q) :=
    Module.finitePresentation_of_projective _ _
  apply exists_basis_of_complex_basis d _ (complexStandardMonomialBasis d t I q)
  exact complexStandardMonomialBasis_apply d t I q

open HironakaActualFormalInitialDiagram HironakaActualTaylorCoordinateNaturality

theorem tangentVariable_mem_fibreFormalIdeal (I : Ideal (HolGerm (ComplexModel (d+t)))) (i : Fin d) :
    MvPowerSeries.X (i.castAdd t) ∈ fibreFormalIdeal d t I := by
  have hg : coordinateGerm i ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) := by
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    rfl
  have hm := Ideal.mem_map_of_mem (tangentPullback d t).toRingHom hg
  change tangentPullback d t (coordinateGerm i) ∈ originalBaseMaximalIdeal d t at hm
  rw [tangentPullback_coordinateGerm] at hm
  have hi : coordinateGerm (i.castAdd t) ∈ I ⊔ originalBaseMaximalIdeal d t := Ideal.mem_sup_right hm
  have h := Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom (d+t)).toRingHom hi
  change actualUnshiftedTaylorAlgHom (d+t) (coordinateGerm (i.castAdd t)) ∈ fibreFormalIdeal d t I at h
  rw [actualUnshiftedTaylor_coordinate] at h
  exact h

theorem standardIndex_tangent_zero (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (α : actualStandardIndex (d+t) (fibreFormalIdeal d t I) q) :
    actualTangentExponent α.val.val = 0 := by
  ext i
  change α.val.val (i.castAdd t) = 0
  by_contra h
  have hx : Finsupp.single (i.castAdd t) 1 ∈
      actualInitialDiagram MonomialOrder.degLex (fibreFormalIdeal d t I) := by
    refine ⟨MvPowerSeries.monomial (Finsupp.single (i.castAdd t) 1) 1,?_,
      actualMonomial_ne_zero _,actualInitialExponent_monomial _ _⟩
    change MvPowerSeries.X (i.castAdd t) ∈ _
    exact tangentVariable_mem_fibreFormalIdeal d t I i
  apply α.property
  apply actualInitialDiagram_upper MonomialOrder.degLex (fibreFormalIdeal d t I) _ _ hx
  intro j
  by_cases hj : j=i.castAdd t
  · subst j
    simpa only [Finsupp.single_eq_same] using Nat.one_le_iff_ne_zero.mpr h
  · simp only [Finsupp.single_eq_of_ne hj,Nat.zero_le]

theorem analyticMonomial_standardIndex_eq_normal (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (α : actualStandardIndex (d+t) (fibreFormalIdeal d t I) q) :
    analyticMonomial (d+t) α.val.val = normalExponentMonomial d t (actualNormalExponent α.val.val) := by
  have ht := standardIndex_tangent_zero d t I q α
  have htz (i : Fin d) : α.val.val (i.castAdd t)=0 := by
    have h := congrArg (fun a : Fin d →₀ ℕ => a i) ht
    simpa only [actualTangentExponent,Finsupp.coe_equivFunOnFinite_symm,Finsupp.coe_zero,Pi.zero_apply] using h
  rw [analyticMonomial,Fin.prod_univ_add]
  simp_rw [htz,pow_zero]
  simp only [Finset.prod_const_one,one_mul,normalExponentMonomial,normalCoordinate,
    actualNormalExponent,Finsupp.coe_equivFunOnFinite_symm]


abbrev normalStandardIndex (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :=
  {γ : normalExponentIndex t q // actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val ∉
    actualInitialDiagram MonomialOrder.degLex (fibreFormalIdeal d t I)}

instance normalStandardIndexFintype (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    Fintype (normalStandardIndex d t I q) := by
  classical
  let := normalExponentFintype t q
  exact inferInstance

theorem degree_joined_zero (γ : Fin t →₀ ℕ) :
    normalExponentDegree (actualJoinedExponent (0 : Fin d →₀ ℕ) γ)=normalExponentDegree γ := by
  simp [normalExponentDegree,actualJoinedExponent,Fin.sum_univ_add]

def normalStandardIndexEquiv (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    normalStandardIndex d t I q ≃ actualStandardIndex (d+t) (fibreFormalIdeal d t I) q where
  toFun γ := ⟨⟨actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val.val,
    by rw [degree_joined_zero];exact γ.val.property⟩,γ.property⟩
  invFun α := ⟨⟨actualNormalExponent α.val.val,by
    have he : actualJoinedExponent (0 : Fin d →₀ ℕ) (actualNormalExponent α.val.val)=α.val.val := by
      rw [← standardIndex_tangent_zero d t I q α]
      exact actualJoinedExponent_split _
    rw [← degree_joined_zero d,he]
    exact α.val.property⟩,by
      have he : actualJoinedExponent (0 : Fin d →₀ ℕ) (actualNormalExponent α.val.val)=α.val.val := by
        rw [← standardIndex_tangent_zero d t I q α]
        exact actualJoinedExponent_split _
      rw [he]
      exact α.property⟩
  left_inv γ := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    simp [actualNormalExponent,actualJoinedExponent]
  right_inv α := by
    apply Subtype.ext
    apply Subtype.ext
    change actualJoinedExponent (0 : Fin d →₀ ℕ) (actualNormalExponent α.val.val)=α.val.val
    rw [← standardIndex_tangent_zero d t I q α]
    exact actualJoinedExponent_split _

theorem exists_normalStandardMonomialBasis (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    [Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q)]
    [Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q)] :
    ∃ b : Module.Basis (normalStandardIndex d t I q)
      (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q),
      ∀ γ, b γ = Ideal.Quotient.mk (I ⊔ normalIdeal d t^q) (normalExponentMonomial d t γ.val.val) := by
  obtain ⟨b,hb⟩ := exists_standardMonomialBasis d t I q
  refine ⟨b.reindex (normalStandardIndexEquiv d t I q).symm,?_⟩
  intro γ
  rw [Module.Basis.reindex_apply,hb,analyticMonomial_standardIndex_eq_normal]
  congr 2
  ext i
  change (actualNormalExponent (actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val.val)) i = γ.val.val i
  simp [actualNormalExponent,actualJoinedExponent]

end Fibre

section OriginalCentre
open scoped Manifold ContDiff
open Hironaka.HolomorphicIdealSheaves OkaRelationSheaf HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicPointJets HironakaRelativeNormalIdeal HironakaRelativeNormalUniformTruncations
  HironakaRelativeNormalMonomialBasis HironakaRelativeNormalAssociatedGraded
  HironakaActualTangentCutLayers HironakaActualJointTangentCuts HironakaStrictFilteredGradedQuotient
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t

theorem exists_original_hs_constant_centre_standard_monomial_bases
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      ∀ q : ℕ, ∃ b : Module.Basis (normalStandardIndex d t I0 q)
        (HolGerm (ComplexModel d)) (originalNormalTruncation d t I0 q),
        ∀ γ, b γ = Ideal.Quotient.mk (I0 ⊔ normalIdeal d t^q) (normalExponentMonomial d t γ.val.val) := by
  obtain ⟨Φ,hsrc,h0,hflat,hG⟩ :=
    exists_original_hs_constant_centre_normal_layers_finite_free d t C x hreg A hA hhs
  refine ⟨Φ,hsrc,h0,hflat,?_⟩
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf A x Φ) 0)
  have hQ := normalTruncations_free_of_layers d t I0 (fun q => by
    change Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I0 q)
    exact (hG q).2)
  change ∀ q : ℕ, ∃ b : Module.Basis (normalStandardIndex d t I0 q)
    (HolGerm (ComplexModel d)) (originalNormalTruncation d t I0 q),
    ∀ γ, b γ = Ideal.Quotient.mk (I0 ⊔ normalIdeal d t^q) (normalExponentMonomial d t γ.val.val)
  intro q
  let : Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d t I0 q) :=
    finite_quotient_sup_normalIdeal_pow d t q I0
  let : Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d t I0 q) := hQ q
  exact exists_normalStandardMonomialBasis d t I0 q

end OriginalCentre
end
end Hironaka.HironakaActualStandardNormalBases
