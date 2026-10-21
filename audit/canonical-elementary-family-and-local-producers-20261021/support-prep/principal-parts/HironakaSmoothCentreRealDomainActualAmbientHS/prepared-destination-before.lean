/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalActualHSConvolution
import Hironaka.Resolution.HironakaSmoothCentreRealDomainOriginalStalkFreeness

/-! Retain the actual original nonlinear centre chart-stalk ambient HS on its genuine real domain. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff DirectSum
namespace Hironaka.HironakaSmoothCentreRealDomainActualAmbientHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicPointJets HironakaRelativeNormalActualHSConvolution
  HironakaSmoothCentreRealDomainOriginalStalkFreeness HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRelativeIdeal
  HironakaSmoothCentreNearbyIdeal
  HironakaHolomorphicJetRankLoci HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalGradedAlgebra HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalNearbyUniformRanks
  HironakaRelativeNormalActualWeightedTruncations
  HironakaHolomorphicJetChartInvariance

section GenuineLocalAlgebras
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
  [IsLocalRing R] [IsLocalRing S]

/-- The genuine original local algebra map retains ALL actual ambient maximal-power quotient classes. -/
def actualLocalAmbientJetAlgEquiv (E : R ≃ₐ[ℂ] S) (I : Ideal R) (s : ℕ) :
    (R ⧸ (I ⊔ IsLocalRing.maximalIdeal R ^ s)) ≃ₐ[ℂ]
      (S ⧸ (Ideal.map E.toRingEquiv.toRingHom I ⊔ IsLocalRing.maximalIdeal S ^ s)) :=
  Ideal.quotientEquivAlg _ _ E (by
    rw [Ideal.map_sup,Ideal.map_pow,
      IsLocalRing.map_maximalIdeal_of_surjective (E : R →+* S) E.surjective]
    rfl)

/-- EVERY original ambient numerator keeps its SAME actual whole algebra image. -/
theorem actualLocalAmbientJetAlgEquiv_mk (E : R ≃ₐ[ℂ] S) (I : Ideal R) (s : ℕ) (g : R) :
    actualLocalAmbientJetAlgEquiv E I s
      (Ideal.Quotient.mk (I ⊔ IsLocalRing.maximalIdeal R ^ s) g) =
        Ideal.Quotient.mk
          (Ideal.map E.toRingEquiv.toRingHom I ⊔ IsLocalRing.maximalIdeal S ^ s) (E g) := rfl

end GenuineLocalAlgebras

/-- The EXISTING original ambient HS is invariant under every genuine original complex germ algebra equivalence. -/
theorem actualAmbientHS_eq_of_genuineAlgEquiv {n : ℕ}
    (E : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n))
    (I : Ideal (HolGerm (ComplexModel n))) (ℓ : ℕ) :
    hilbertSamuelValue (Ideal.map E.toRingEquiv.toRingHom I) ℓ = hilbertSamuelValue I ℓ :=
  (actualLocalAmbientJetAlgEquiv E I (ℓ+1)).toLinearEquiv.finrank_eq.symm

section Manifold
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- ANY fixed actual nonlinear flattening retains the SAME WHOLE original chart-stalk ambient HS at EVERY true target point. -/
theorem fixed_real_original_whole_stalk_ambient_hs_dictionary
    (A : GermIdeal n M) (hA : A.IsCoherent) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (a : ComplexModel n) (ha : a ∈ Φ.target) (ℓ : ℕ) :
    let y := actualFlatteningInverseMap x Φ a
    let hy := actualNearbyPoint_mem_chart_source x Φ hsrc a ha
    hilbertSamuelValue (wholeChartStalkIdeal A x y hy) ℓ =
      hilbertSamuelValue
        (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) a)) ℓ := by
  dsimp only
  have hmap := (whole_original_stalk_dictionary_at_actual_target A hA x Φ hsrc a ha).1
  rw [← hmap]
  exact actualAmbientHS_eq_of_genuineAlgEquiv (actualNearbyGermEquiv Φ a ha) _ ℓ

end Manifold

open HironakaSmoothCentreRealDomainCoefficientAlgebra
  HironakaRelativeNormalCoefficientFunctionAlgebra HironakaRelativeNormalCoefficientAlgebraNearbyFreeness
  HironakaRelativeNormalUniformLocalization HironakaRelativeNormalUniformTruncations
attribute [local instance] coefficientSubalgebraRing

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ONLY original regular-centre geometry and coherence give ONE true real open and ALL genuine uniform normal-layer ranks. -/
theorem exists_original_regular_real_uniform_degree_ranks
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    let := tangentAlgebra d t
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ U : Set (ComplexModel d), ∃ r : ℕ → ℕ, IsOpen U ∧
        (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
        (∀ a ∈ U, tangentInclusion d t a ∈ Φ.target ∩ complexCoordinatePlane (d+t) d) ∧
        ∀ a ∈ U, ∀ q : ℕ,
          let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
            (actualFlattenedOriginalSheaf A x Φ) (tangentInclusion d t a))
          Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t Ia q) ∧
          Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t Ia q) ∧
          Module.finrank (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t Ia q) = r q := by
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
  let U := {a : ComplexModel d | a ∈ W ∧ g a ≠ 0}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    have hcont : ContinuousAt g a := ((C0.val c).property a (hWB ha.1)).self_of_nhds.continuousAt
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
  refine ⟨Φ,hsrc,h0Φ,hflat,U,r,hU,hmeet,(fun a ha => hpoint a (hWB ha.1)),?_⟩
  intro a ha q
  have hvalue : (ρ a ha.1) b = coefficientGermHom d B a (hWB ha.1) (C0.val c) := by
    rw [← hcb]
    exact congrArg (fun f : C0 →ₐ[ℂ] HolGerm (ComplexModel d) => f c) (hρ a ha.1)
  have hunit : IsUnit ((ρ a ha.1) b) := by
    apply (HolGerm.isUnit_iff_eval_ne_zero ((ρ a ha.1) b)).mpr
    rw [hvalue]
    change g (actualAffineTranslation d a 0) ≠ 0
    simpa only [actualAffineTranslation_zero] using ha.2
  have hH : Ideal.map (MvPolynomial.map (ρ a ha.1).toRingHom) H =
      originalNormalInitialIdeal d t
        (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion d t a))) :=
    hideal a ha.1
  let := uniformDegreeStandardExponentFintype (K := FractionRing D) t
    (MonomialOrder.degLex (σ := Fin t)) H q
  let bv := originalDegreeCoefficientImageMonomialBasis
    (K := FractionRing D) d t
    (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion d t a)))
    (MonomialOrder.degLex (σ := Fin t)) H (ρ a ha.1).toRingHom hunit hH q
  exact ⟨Module.Free.of_basis bv, Module.Finite.of_basis bv, Module.finrank_eq_nat_card_basis bv⟩

/-- ONLY original geometry and coherence give the ACTUAL original nonlinear centre ambient HS convolution on one SAME real open. -/
theorem exists_original_regular_real_actual_ambient_hs_convolution
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ U : Set (ComplexModel d), ∃ r : ℕ → ℕ, IsOpen U ∧
        (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
        ∃ hpoint : ∀ a ∈ U, tangentInclusion d t a ∈ Φ.target ∩ complexCoordinatePlane (d+t) d,
        ∀ a (ha : a ∈ U),
          let a0 := tangentInclusion d t a
          let y := actualFlatteningInverseMap x Φ a0
          let hy := actualNearbyPoint_mem_chart_source x Φ hsrc a0 (hpoint a ha).1
          y ∈ C ∧ ∀ ℓ : ℕ,
            hilbertSamuelValue (wholeChartStalkIdeal A x y hy) ℓ =
              ∑ q : Fin (ℓ+1), r q.val * (d+ℓ-q.val).choose d := by
  classical
  let := tangentAlgebra d t
  let : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
    IsScalarTower.of_algHom (tangentPullback d t)
  obtain ⟨Φ,hsrc,h0,hflat,U,r,hU,hmeet,hpoint,hdegree⟩ :=
    exists_original_regular_real_uniform_degree_ranks C x hreg A hA
  refine ⟨Φ,hsrc,h0,hflat,U,r,hU,hmeet,hpoint,?_⟩
  intro a ha
  dsimp only
  have hdom := actualNearbyPoint_mem_flatDomain x Φ hsrc (tangentInclusion d t a) (hpoint a ha).1
  have himage : Φ.toFun (chartAt (ComplexModel (d+t)) x
      (actualFlatteningInverseMap x Φ (tangentInclusion d t a))) = tangentInclusion d t a := by
    rw [actualNearbyPoint_chart_value x Φ hsrc _ (hpoint a ha).1,Φ.right_inv _ (hpoint a ha).1]
  refine ⟨(hflat hdom.1 hdom.2).mpr (by rw [himage]; exact (hpoint a ha).2),?_⟩
  intro ℓ
  rw [fixed_real_original_whole_stalk_ambient_hs_dictionary A hA x Φ hsrc _ (hpoint a ha).1 ℓ]
  let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf A x Φ) (tangentInclusion d t a))
  let : ∀ q, Module.Free (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) Ia (normalIdeal d t) q) :=
    fun q => (hdegree a ha q).1
  let : ∀ q, Module.Finite (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) Ia (normalIdeal d t) q) :=
    fun q => (hdegree a ha q).2.1
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
    (hdegree a ha q.val).2.2
  rw [hr]

/-- The SAME actual original nonlinear centre points have equal whole ambient HS at EVERY order. -/
theorem exists_original_regular_real_actual_ambient_hs_constancy
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ U : Set (ComplexModel d), IsOpen U ∧
        (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
        ∃ hpoint : ∀ a ∈ U, tangentInclusion d t a ∈ Φ.target ∩ complexCoordinatePlane (d+t) d,
        ∀ a (ha : a ∈ U),
          let ya := actualFlatteningInverseMap x Φ (tangentInclusion d t a)
          let hya := actualNearbyPoint_mem_chart_source x Φ hsrc _ (hpoint a ha).1
          ya ∈ C ∧ ∀ b (hb : b ∈ U), ∀ ℓ : ℕ,
            let yb := actualFlatteningInverseMap x Φ (tangentInclusion d t b)
            let hyb := actualNearbyPoint_mem_chart_source x Φ hsrc _ (hpoint b hb).1
            hilbertSamuelValue (wholeChartStalkIdeal A x ya hya) ℓ =
              hilbertSamuelValue (wholeChartStalkIdeal A x yb hyb) ℓ := by
  obtain ⟨Φ,hsrc,_h0,_hflat,U,r,hU,hmeet,hpoint,hvalue⟩ :=
    exists_original_regular_real_actual_ambient_hs_convolution C x hreg A hA
  exact ⟨Φ,hsrc,U,hU,hmeet,hpoint,fun a ha =>
    ⟨(hvalue a ha).1,fun b hb ℓ => ((hvalue a ha).2 ℓ).trans ((hvalue b hb).2 ℓ).symm⟩⟩

end OriginalCentre

section IntrinsicOriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ONLY original geometry and coherence give the EXISTING intrinsic hilbertSamuelAt at SAME genuine nonlinear centre points and ALL orders. -/
theorem exists_original_regular_real_intrinsic_ambient_hs_convolution
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ U : Set (ComplexModel d), ∃ r : ℕ → ℕ, IsOpen U ∧
        (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
        ∀ a ∈ U,
          let y := actualFlatteningInverseMap x Φ (tangentInclusion d t a)
          y ∈ C ∧ ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ =
            ∑ q : Fin (ℓ+1), r q.val * (d+ℓ-q.val).choose d := by
  obtain ⟨Φ,hsrc,_h0,_hflat,U,r,hU,hmeet,hpoint,hvalue⟩ :=
    exists_original_regular_real_actual_ambient_hs_convolution C x hreg A hA
  refine ⟨Φ,U,r,hU,hmeet,?_⟩
  intro a ha
  refine ⟨(hvalue a ha).1,?_⟩
  intro ℓ
  rw [hilbertSamuelAt_eq_fixedChart A x _
    (actualNearbyPoint_mem_chart_source x Φ hsrc _ (hpoint a ha).1) ℓ]
  exact (hvalue a ha).2 ℓ

/-- The true EXISTING intrinsic original ambient HS agrees at ALL orders on the SAME actual nonlinear centre family. -/
theorem exists_original_regular_real_intrinsic_ambient_hs_constancy
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ U : Set (ComplexModel d), IsOpen U ∧
        (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
        ∀ a ∈ U,
          actualFlatteningInverseMap x Φ (tangentInclusion d t a) ∈ C ∧
          ∀ b ∈ U, ∀ ℓ : ℕ,
            hilbertSamuelAt A (actualFlatteningInverseMap x Φ (tangentInclusion d t a)) ℓ =
              hilbertSamuelAt A (actualFlatteningInverseMap x Φ (tangentInclusion d t b)) ℓ := by
  obtain ⟨Φ,U,r,hU,hmeet,hvalue⟩ :=
    exists_original_regular_real_intrinsic_ambient_hs_convolution C x hreg A hA
  exact ⟨Φ,U,hU,hmeet,fun a ha =>
    ⟨(hvalue a ha).1,fun b hb ℓ => ((hvalue a ha).2 ℓ).trans ((hvalue b hb).2 ℓ).symm⟩⟩

end IntrinsicOriginalCentre
end
end Hironaka.HironakaSmoothCentreRealDomainActualAmbientHS
