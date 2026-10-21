/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualAmbientHS
/-! Retain the genuine common holomorphic denominator and its ACTUAL nonzero
locus for every original normal degree/intrinsic HS order. No caller certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff DirectSum
namespace Hironaka.HironakaOriginalAnalyticHSGenericDenominator
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicPointJets HironakaRelativeNormalActualHSConvolution
  HironakaSmoothCentreRealDomainOriginalStalkFreeness HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRelativeIdeal HironakaSmoothCentreNearbyIdeal
  HironakaHolomorphicJetRankLoci HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalGradedAlgebra HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalNearbyUniformRanks
  HironakaRelativeNormalActualWeightedTruncations HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaSmoothCentreRealDomainCoefficientAlgebra HironakaRelativeNormalUniformLocalization
  HironakaRelativeNormalCoefficientFunctionAlgebra HironakaRelativeNormalCoefficientAlgebraNearbyFreeness
  HironakaRelativeNormalUniformTruncations
attribute [local instance] coefficientSubalgebraRing

/-- A genuine single actual holomorphic equation gives its literal analytic zero set. -/
theorem actual_holomorphic_zero_analytic {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (g : M → ℂ) (hg : ∀ x,HolomorphicAt n g x) :
    IsComplexAnalyticSubset (n := n) {x | g x=0} := by
  have hdiff : MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) g univ :=
    fun x _ => (hg x).mdifferentiableAt.mdifferentiableWithinAt
  intro x
  refine ⟨{ generatorCount := 1
            generator := fun _ z => g ((complexChartAt (n := n) x).val.symm z)
            coordinateNeighborhood := (complexChartAt (n := n) x).val.target
            isOpen_coordinateNeighborhood := (complexChartAt (n := n) x).val.open_target
            center_mem_coordinateNeighborhood := (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
            coordinateNeighborhood_subset_target := subset_rfl
            generator_holomorphic := fun _ => ?_
            zeroLocus := ?_ }⟩
  · simpa only [preimage_univ,inter_univ] using differentiableOn_comp_chartSymm x hdiff
  · intro y hy _
    simp only [(complexChartAt (n := n) x).val.left_inv hy]
    exact ⟨fun h _ => h,fun h => h 0⟩

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- ONLY original inputs retain the actual nonzero-germ denominator and ENTIRE
literal nonzero locus of the SAME whole original uniform normal-degree ranks. -/
theorem exists_original_analytic_denominator_uniform_degrees
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    let := tangentAlgebra d t
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0 ∧
      (∀ {y : M},y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ (W : Opens (ComplexModel d)),(0 : ComplexModel d) ∈ W ∧
      ∃ g : ComplexModel d → ℂ,(∀ a ∈ W,HolomorphicAt d g a) ∧
        (g : Germ (𝓝 (0 : ComplexModel d)) ℂ) ≠ 0 ∧
      ∃ r : ℕ → ℕ,(∀ a ∈ W,tangentInclusion d t a ∈ Φ.target ∩ complexCoordinatePlane (d+t) d) ∧
      ∀ a ∈ W,g a ≠ 0 → ∀ q : ℕ,
        let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf A x Φ) (tangentInclusion d t a))
        Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t Ia q) ∧
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t Ia q) ∧
        Module.finrank (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t Ia q)=r q := by
  classical
  let := tangentAlgebra d t
  obtain ⟨Φ,hsrc,h0Φ,hflat,B,_hB,h0,hpoint,C0,_hC,hD,_hDf,W,hW,h0W,hWB,ρ,Q,_hhom,hρ,hideal⟩ :=
    exists_original_regular_real_common_domain_initial_family C x hreg A hA
  let F := actualFlattenedOriginalSheaf A x Φ
  let D := coefficientOriginAlgebra d B h0 C0
  let : IsDomain D := hD
  let : Field (FractionRing D) := FractionRing.field D
  let H : Ideal (MvPolynomial (Fin t) D) := Ideal.span (range Q)
  let b := uniformLeadingDenominator (K := FractionRing D) t (MonomialOrder.degLex (σ := Fin t)) H
  have hb : b ≠ 0 := uniformLeadingDenominator_ne_zero _ _ _
  obtain ⟨c, hcb⟩ := Ideal.Quotient.mk_surjective b
  let g : ComplexModel d → ℂ := (C0.val c).val
  have hc0 : ((coefficientGermHom d B 0 h0).comp C0.val) c ≠ 0 := by
    intro hz
    have hc : c ∈ coefficientOriginKernel d B h0 C0 := hz
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
  let r : ℕ → ℕ := fun q => Nat.card
    (uniformDegreeStandardExponentIndex (K := FractionRing D) t
      (MonomialOrder.degLex (σ := Fin t)) H q)
  refine ⟨Φ,hsrc,h0Φ,hflat,⟨W,hW⟩,h0W,g,?_,hg0,r,(fun a ha => hpoint a (hWB ha)),?_⟩
  · intro a ha
    exact ((C0.val c).property a (hWB ha)).mono fun _ hz => hz.mdifferentiableAt
  intro a ha hga q
  have hvalue : (ρ a ha) b = coefficientGermHom d B a (hWB ha) (C0.val c) := by
    rw [← hcb]
    exact congrArg (fun f : C0 →ₐ[ℂ] HolGerm (ComplexModel d) => f c) (hρ a ha)
  have hunit : IsUnit ((ρ a ha) b) := by
    apply (HolGerm.isUnit_iff_eval_ne_zero ((ρ a ha) b)).mpr
    rw [hvalue]
    change g (actualAffineTranslation d a 0) ≠ 0
    simpa only [actualAffineTranslation_zero] using hga
  have hH : Ideal.map (MvPolynomial.map (ρ a ha).toRingHom) H =
      originalNormalInitialIdeal d t
        (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion d t a))) :=
    hideal a ha
  let := uniformDegreeStandardExponentFintype (K := FractionRing D) t
    (MonomialOrder.degLex (σ := Fin t)) H q
  let bv := originalDegreeCoefficientImageMonomialBasis
    (K := FractionRing D) d t
    (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion d t a)))
    (MonomialOrder.degLex (σ := Fin t)) H (ρ a ha).toRingHom hunit hH q
  exact ⟨Module.Free.of_basis bv, Module.Finite.of_basis bv, Module.finrank_eq_nat_card_basis bv⟩

/-- The SAME real denominator's ENTIRE nonzero locus has the EXISTING intrinsic
ambient HS convolution at ALL orders, with its literal analytic zero set retained. -/
theorem exists_original_analytic_denominator_intrinsic_hs
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0 ∧
      (∀ {y : M},y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ (W : Opens (ComplexModel d)),(0 : ComplexModel d) ∈ W ∧
      ∃ g : ComplexModel d → ℂ,(∀ a ∈ W,HolomorphicAt d g a) ∧
        (g : Germ (𝓝 (0 : ComplexModel d)) ℂ) ≠ 0 ∧
        IsComplexAnalyticSubset (n := d) {a : W | g a=0} ∧
      ∃ r : ℕ → ℕ,∀ a ∈ W,g a ≠ 0 →
        let y := actualFlatteningInverseMap x Φ (tangentInclusion d t a)
        y ∈ C ∧ ∀ ℓ : ℕ,hilbertSamuelAt A y ℓ=∑ q : Fin (ℓ+1),r q.val*(d+ℓ-q.val).choose d := by
  let := tangentAlgebra d t
  let : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
    IsScalarTower.of_algHom (tangentPullback d t)
  obtain ⟨Φ,hsrc,h0,hflat,W,h0W,g,hg,hgnz,r,hpoint,hdegree⟩ :=
    exists_original_analytic_denominator_uniform_degrees C x hreg A hA
  have hzero : IsComplexAnalyticSubset (n := d) {a : W | g a=0} :=
    actual_holomorphic_zero_analytic (fun a : W => g a)
      (fun a => (holomorphicAt_comp_val_iff W).mpr (hg a a.property))
  refine ⟨Φ,hsrc,h0,hflat,W,h0W,g,hg,hgnz,hzero,r,?_⟩
  intro a ha hga
  dsimp only
  have hdom := actualNearbyPoint_mem_flatDomain x Φ hsrc (tangentInclusion d t a) (hpoint a ha).1
  have himage : Φ.toFun (chartAt (ComplexModel (d+t)) x
      (actualFlatteningInverseMap x Φ (tangentInclusion d t a))) = tangentInclusion d t a := by
    rw [actualNearbyPoint_chart_value x Φ hsrc _ (hpoint a ha).1,Φ.right_inv _ (hpoint a ha).1]
  refine ⟨(hflat hdom.1 hdom.2).mpr (by rw [himage]; exact (hpoint a ha).2),?_⟩
  intro ℓ
  rw [hilbertSamuelAt_eq_fixedChart A x _ (actualNearbyPoint_mem_chart_source x Φ hsrc _ (hpoint a ha).1) ℓ]
  rw [fixed_real_original_whole_stalk_ambient_hs_dictionary A hA x Φ hsrc _ (hpoint a ha).1 ℓ]
  let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf A x Φ) (tangentInclusion d t a))
  let : ∀ q, Module.Free (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) Ia (normalIdeal d t) q) :=
    fun q => (hdegree a ha hga q).1
  let : ∀ q, Module.Finite (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) Ia (normalIdeal d t) q) :=
    fun q => (hdegree a ha hga q).2.1
  let : ∀ q : Fin (ℓ+1), Module.Finite ℂ
      (actualWeightedLayerQuotient (B := HolGerm (ComplexModel d)) Ia (normalIdeal d t)
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) (ℓ+1) q.val) :=
    fun q => actualOriginalWeightedLayerFinite d t Ia ℓ q.val (Nat.le_of_lt_succ q.isLt)
  let : ∀ q : Fin (ℓ+1), Module.Free ℂ
      (actualWeightedLayerQuotient (B := HolGerm (ComplexModel d)) Ia (normalIdeal d t)
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) (ℓ+1) q.val) :=
    fun _ => inferInstance
  let ew := actualAmbientWeightedLayersEquiv (B := HolGerm (ComplexModel d))
    Ia (normalIdeal d t) (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) (ℓ+1)
  let em := Ideal.quotientEquivAlgOfEq ℂ
    (congrArg (fun J => Ia ⊔ J) (originalActualMixedPower_eq_maximalIdeal_power d t (ℓ+1)).symm)
  let e := em.toLinearEquiv.trans (ew.restrictScalars ℂ)
  change Module.finrank ℂ (HolGerm (ComplexModel (d+t)) ⧸
    (Ia ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ (ℓ+1))) = _
  rw [e.finrank_eq,Module.finrank_directSum]
  apply Finset.sum_congr rfl
  intro q _
  rw [actualOriginalWeightedLayerDimension d t Ia ℓ q.val (Nat.le_of_lt_succ q.isLt)]
  have hr : Module.finrank (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) Ia (normalIdeal d t) q.val) = r q.val :=
    (hdegree a ha hga q.val).2.2
  rw [hr]


end OriginalCentre
end
end Hironaka.HironakaOriginalAnalyticHSGenericDenominator
