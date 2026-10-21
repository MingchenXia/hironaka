/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualStandardNormalBases
import Hironaka.Resolution.HironakaActualRelativeFormalQuotients
import Hironaka.Resolution.HironakaActualReducedNormalSupport
import Hironaka.Resolution.HironakaActualNormalFibreDiagramCompare
import Hironaka.Resolution.HironakaActualCoupledNormalFreeness
import Mathlib.LinearAlgebra.TensorProduct.Basis
/-!
# Literal normal monomial independence and actual canonical reduced-vertex powers

Actual analytic standard normal monomial bases are base-changed through the
proved whole relative formal quotient dictionary. Their exact numerator
formula gives literal formal monomial bases. Restricting the actual finite
coefficient sum to the genuine fibre standard labels proves injectivity of
the named formal standard-normal monomial map. The actual fibre/original
pure-normal diagram comparison and reduced-support theorem then force each
whole canonical reduced vertex series into its genuine normal ideal power.

The original-only endpoint uses one coupled original constant-HS centre
family for both actual normal freeness and initial tangential stability.
No vertex-power, independence or normal-flatness certificate is supplied.
Geometric Bennett transformation and the singular resolution driver are
separate subsequent results.
-/

set_option autoImplicit false
open Set TensorProduct
open scoped TensorProduct
namespace Hironaka.HironakaActualStandardNormalIndependence
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalUniformTruncations HironakaActualCoefficientPresentationCentrePower
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalInitialDiagram
  HironakaActualRelativeTaylorCoefficients HironakaActualFormalNormalTruncations
  HironakaActualStandardNormalBases HironakaActualRelativeFormalQuotients
  HironakaActualReducedNormalSupport HironakaActualNormalFibreDiagramCompare
  HironakaActualHomogeneousInitialHS HironakaActualReducedFormalStandardBasis
  HironakaRelativeNormalAssociatedGraded HironakaActualJointTangentCuts
variable (d t : ℕ)
local instance (q : ℕ) : Fintype (normalExponentIndex t q) := normalExponentFintype t q
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t
local instance : Algebra (HolGerm (ComplexModel d)) (MvPowerSeries (Fin d) ℂ) :=
  (actualUnshiftedTaylorAlgHom d).toRingHom.toAlgebra
local instance : Algebra (MvPowerSeries (Fin d) ℂ) (MvPowerSeries (Fin (d+t)) ℂ) :=
  (MvPowerSeries.rename (Fin.castAdd t : Fin d → Fin (d+t))).toRingHom.toAlgebra

theorem exists_formalNormalStandardBasis (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    [Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q)]
    [Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q)] :
    ∃ b : Module.Basis (normalStandardIndex d t I q) (MvPowerSeries (Fin d) ℂ)
      (MvPowerSeries (Fin (d+t)) ℂ ⧸
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I ⊔
          actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)),
      ∀ γ, b γ = Ideal.Quotient.mk _
        (MvPowerSeries.monomial (actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val.val) 1) := by
  obtain ⟨b,hb⟩ := exists_normalStandardMonomialBasis d t I q
  refine ⟨(b.baseChange (MvPowerSeries (Fin d) ℂ)).map
    (relativeFormalQuotientEquiv d t q I),?_⟩
  intro γ
  rw [Module.Basis.map_apply,Module.Basis.baseChange_apply,hb]
  change relativeFormalQuotientEquiv d t q I
    ((1 : MvPowerSeries (Fin d) ℂ) ⊗ₜ[HolGerm (ComplexModel d)]
      Ideal.Quotient.mk (I ⊔ normalIdeal d t^q) (normalExponentMonomial d t γ.val.val)) = _
  rw [relativeFormalQuotientEquiv_tmul_mk,one_smul,actualUnshiftedTaylor_normalExponentMonomial]

private theorem standardNormalMonomialMap_eq_restricted_sum
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (hdiag : ∀ γ : Fin t →₀ ℕ,
      actualJoinedExponent (0 : Fin d →₀ ℕ) γ ∈
        actualInitialDiagram MonomialOrder.degLex (fibreFormalIdeal d t I) ↔
      actualJoinedExponent (0 : Fin d →₀ ℕ) γ ∈
        actualInitialDiagram MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I))
    (a : formalStandardNormalCoefficients d t MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) q) :
    standardNormalMonomialMap d t MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) q a =
      ∑ γ : normalStandardIndex d t I q, a.val γ.val • Ideal.Quotient.mk _
        (MvPowerSeries.monomial (actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val.val) 1) := by
  classical
  let K := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I
  let D := K ⊔ actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q
  let f (γ : normalExponentIndex t q) := a.val γ • Ideal.Quotient.mk D
    (MvPowerSeries.monomial (actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val) 1)
  change Ideal.Quotient.mk D (formalNormalCombination d t q a.val) = _
  change (Ideal.Quotient.mkₐ (MvPowerSeries (Fin d) ℂ) D) (∑ γ : normalExponentIndex t q,
    a.val γ • MvPowerSeries.monomial (actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val) 1) = _
  rw [map_sum]
  simp_rw [map_smul]
  change (∑ γ : normalExponentIndex t q, f γ) = ∑ γ : normalStandardIndex d t I q, f γ.val
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun γ : normalExponentIndex t q => actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val ∉
      actualInitialDiagram MonomialOrder.degLex (fibreFormalIdeal d t I)) f
  have hz : (∑ γ : {γ : normalExponentIndex t q // ¬ (actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val ∉
      actualInitialDiagram MonomialOrder.degLex (fibreFormalIdeal d t I))}, f γ.val)=0 := by
    apply Finset.sum_eq_zero
    intro γ _
    have hγ := (hdiag γ.val.val).mp (Classical.not_not.mp γ.property)
    dsimp only [f]
    rw [a.property γ.val hγ,zero_smul]
  simpa only [hz,add_zero] using hs.symm

theorem standardNormalMonomialMap_injective_of_fibre_diagram
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    [Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q)]
    [Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q)]
    (hdiag : ∀ γ : Fin t →₀ ℕ,
      actualJoinedExponent (0 : Fin d →₀ ℕ) γ ∈
        actualInitialDiagram MonomialOrder.degLex (fibreFormalIdeal d t I) ↔
      actualJoinedExponent (0 : Fin d →₀ ℕ) γ ∈
        actualInitialDiagram MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)) :
    Function.Injective (standardNormalMonomialMap d t MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) q) := by
  obtain ⟨b,hb⟩ := exists_formalNormalStandardBasis d t I q
  have hli : LinearIndependent (MvPowerSeries (Fin d) ℂ)
      (fun γ : normalStandardIndex d t I q => Ideal.Quotient.mk
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I ⊔
          actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)
        (MvPowerSeries.monomial (actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val.val) 1)) := by
    have he : (b : normalStandardIndex d t I q → _) =
        (fun γ : normalStandardIndex d t I q => Ideal.Quotient.mk
          (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I ⊔
            actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)
          (MvPowerSeries.monomial (actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val.val) 1)) := funext hb
    rw [← he]
    exact b.linearIndependent
  intro a c hac
  have hsum := (standardNormalMonomialMap_eq_restricted_sum d t I q hdiag a).symm.trans
    (hac.trans (standardNormalMonomialMap_eq_restricted_sum d t I q hdiag c))
  have he := hli.fintypeLinearCombination_injective hsum
  apply Subtype.ext
  funext γ
  by_cases hγ : actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val ∈
      actualInitialDiagram MonomialOrder.degLex (fibreFormalIdeal d t I)
  · exact (a.property γ ((hdiag γ.val).mp hγ)).trans (c.property γ ((hdiag γ.val).mp hγ)).symm
  · exact congrFun he ⟨γ,hγ⟩


theorem actual_reduced_vertices_mem_normal_powers_of_normal_free_and_initial_stable
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hfree : ∀ q : ℕ, Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q))
    (hD : ∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ),
      F ∈ actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) →
      MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈
        actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)) :
    ∀ a : actualInitialVertices MonomialOrder.degLex (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I),
      actualReducedVertexSeries MonomialOrder.degLex (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a ∈
        actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^
          Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val := by
  have hQ := normalTruncations_free_of_layers d t I (fun q => by
    change Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q)
    exact hfree q)
  apply all_actualReducedVertexSeries_mem_normal_power_of_standardNormalMonomialMap_injective
    d t MonomialOrder.degLex _
  intro q
  let : Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q) :=
    finite_quotient_sup_normalIdeal_pow d t q I
  let : Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d t I q) := hQ q
  apply standardNormalMonomialMap_injective_of_fibre_diagram d t I q
  intro γ
  exact pure_normal_fibre_diagram_iff d t I hD γ

section OriginalCentre
open scoped Manifold ContDiff
open Hironaka.HolomorphicIdealSheaves OkaRelationSheaf HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicPointJets HironakaActualCoupledNormalFreeness
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

theorem exists_original_hs_constant_centre_reduced_normal_powers
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
      let K0 := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0
      ∀ a : actualInitialVertices MonomialOrder.degLex K0,
        actualReducedVertexSeries MonomialOrder.degLex K0 a ∈
          actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^
            Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val := by
  obtain ⟨Φ,hsrc,h0,hflat,hG,hD,_hDP,_hN⟩ :=
    exists_original_hs_constant_centre_coupled_normal_data C x hreg A hA hhs
  refine ⟨Φ,hsrc,h0,hflat,?_⟩
  exact actual_reduced_vertices_mem_normal_powers_of_normal_free_and_initial_stable d t _
    (fun q => (hG q).2) hD

end OriginalCentre
end
end Hironaka.HironakaActualStandardNormalIndependence
