/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticStrictGenerators
import Hironaka.Resolution.HironakaActualCanonicalCentreCompatibility
import Hironaka.Resolution.HironakaActualFiniteCoefficientIdeals

/-! Internally produced original analytic vertex coefficients and geometric coefficient-cosupport consumers. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAnalyticVertexCoefficientData
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualOriginalFormalTaylor HironakaActualFormalInitialDiagram
  HironakaActualCoefficientPresentationCentrePower HironakaActualCoefficientReducedStrictGenerators
  HironakaActualAnalyticBlowupTaylor HironakaActualFormalCoordinatePowerDivision
  HironakaActualReducedFormalStandardBasis HironakaActualReducedBasisDivision
  HironakaActualAnalyticCentreVertexFamily HironakaActualCanonicalCentreCompatibility
  HironakaActualAnalyticStrictGenerators HironakaActualFiniteCoefficientIdeals
  HironakaActualLocalCoefficientStrictGenerators HironakaRelativeNormalMonomialBasis
  HironakaSmoothCentreCoherentDomain OkaRelationSheaf GermIdealOrder
  HironakaActualFormalStrictGenerators

/-- Genuine original analytic monic generators and actual coefficient functions on one real open domain. -/
structure ActualAnalyticVertexCoefficientData (k s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((k+s)+t)))) where
  generator : actualInitialVertices MonomialOrder.degLex
    (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I) → HolGerm (ComplexModel ((k+s)+t))
  member : ∀ a,generator a ∈ I
  nonzero : ∀ a,actualUnshiftedTaylorAlgHom ((k+s)+t) (generator a) ≠ 0
  initial : ∀ a,actualInitialExponent MonomialOrder.degLex
    (actualUnshiftedTaylorAlgHom ((k+s)+t) (generator a)) (nonzero a)=a.val
  monic : ∀ a,MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom ((k+s)+t) (generator a))=1
  generates : Ideal.span (range generator)=I
  domain : Set (ComplexModel (k+s))
  isOpen_domain : IsOpen domain
  zero_mem_domain : (0 : ComplexModel (k+s)) ∈ domain
  coefficient : actualInitialVertices MonomialOrder.degLex
    (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I) →
      (Fin t →₀ ℕ) → ComplexModel (k+s) → ℂ
  holomorphic : ∀ a γ,HolAt (coefficient a γ) 0
  regular : ∀ a γ,actualNormalDegree γ<actualCoefficientCentreVertexWeight k s t a.val →
    MDifferentiableOn 𝓘(ℂ,ComplexModel (k+s)) 𝓘(ℂ,ℂ) (coefficient a γ) domain
  coherent : ∀ a γ,actualNormalDegree γ<actualCoefficientCentreVertexWeight k s t a.val →
    CoherentOn (actualPrincipalCoefficientIdeal (k+s) (coefficient a γ)) domain
  coefficient_member : ∀ a γ,actualNormalDegree γ<actualCoefficientCentreVertexWeight k s t a.val →
    (actualPrincipalCoefficientIdeal (k+s) (coefficient a γ)).mem 0 (coefficient a γ)
  coefficient_eq : ∀ a γ,actualFormalNormalCoefficient
    (actualUnshiftedTaylorAlgHom ((k+s)+t) (generator a)) γ=
      actualUnshiftedTaylorAlgHom (k+s) (HolGerm.mk (coefficient a γ) (holomorphic a γ))

/-- Only the original analytic ideal is supplied: all genuine generators, functions and their domain are produced. -/
theorem nonempty_actualAnalyticVertexCoefficientData (k s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((k+s)+t)))) :
    Nonempty (ActualAnalyticVertexCoefficientData k s t I) := by
  let n := (k+s)+t
  let J := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  have hempty (a : actualInitialVertices MonomialOrder.degLex J) :
      actualReducedVertexSeries MonomialOrder.degLex J a ∈ actualFormalCoordinateIdeal n ∅ ^
        Finsupp.weight (actualCoordinateWeight ∅) a.val := by
    simp [actualCoordinateWeight,Finsupp.weight_eq_sum]
  obtain ⟨G,hG,hspan⟩ := exists_actual_analytic_centre_vertex_family n I ∅ hempty
  let q := ∑ a : actualInitialVertices MonomialOrder.degLex J,
    actualCoefficientCentreVertexWeight k s t a.val
  have hle (a : actualInitialVertices MonomialOrder.degLex J) :
      actualCoefficientCentreVertexWeight k s t a.val ≤ q :=
    Finset.single_le_sum
      (f := fun a : actualInitialVertices MonomialOrder.degLex J =>
        actualCoefficientCentreVertexWeight k s t a.val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  obtain ⟨U,hU,h0,c,hc,hd,hT,_⟩ := exists_actual_finite_local_coefficient_ideals (k+s) t q G
  have hd' (a : actualInitialVertices MonomialOrder.degLex J) (γ : Fin t →₀ ℕ)
      (hγ : actualNormalDegree γ<actualCoefficientCentreVertexWeight k s t a.val) :=
    hd a γ (lt_of_lt_of_le hγ (hle a))
  exact ⟨{
    generator := G
    member := fun a => (hG a).1
    nonzero := fun a => (hG a).2.2.choose
    initial := fun a => (hG a).2.2.choose_spec.1
    monic := fun a => (hG a).2.2.choose_spec.2
    generates := hspan
    domain := U
    isOpen_domain := hU
    zero_mem_domain := h0
    coefficient := c
    holomorphic := hc
    regular := fun a γ hγ => (hd' a γ hγ).1
    coherent := fun a γ hγ => (hd' a γ hγ).2.1
    coefficient_member := fun a γ hγ => (hd' a γ hγ).2.2
    coefficient_eq := hT }⟩

/-- Actual original coefficient cosupport derives canonical compatibility before constructing whole analytic strict generators. -/
theorem exists_actual_original_coefficient_strict_generators (k s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((k+s)+t)))) :
    ∃ P : ActualAnalyticVertexCoefficientData k s t I,
      (∀ a γ,actualNormalDegree γ<actualCoefficientCentreVertexWeight k s t a.val →
        P.domain ∩ complexCoordinatePlane (k+s) k ⊆
          cosupport (k+s) univ (actualPrincipalCoefficientIdeal (k+s) (P.coefficient a γ))
            (actualCoefficientCentreVertexWeight k s t a.val-actualNormalDegree γ)) →
      (∀ a : actualInitialVertices MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I),
        actualReducedVertexSeries MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I) a ∈
          actualFormalCoordinateIdeal ((k+s)+t) (actualCoefficientCentreVariables k s t) ^
            actualCoefficientCentreVertexWeight k s t a.val) ∧
      ∀ (e : Fin ((k+s)+t)) (he : e ∈ actualCoefficientCentreVariables k s t)
        (b : Fin ((k+s)+t) → ℂ),
        ∃ H : actualInitialVertices MonomialOrder.degLex
            (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I) → HolGerm (ComplexModel ((k+s)+t)),
          actualAnalyticNormalizedMemberIdeal I (actualCoefficientCentreVariables k s t) e b=Ideal.span (range H) ∧
          Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom
              (actualAnalyticNormalizedMemberIdeal I (actualCoefficientCentreVariables k s t) e b)=
            actualFormalStrictTransform (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I)
              (actualCoefficientCentreVariables k s t) e he b := by
  obtain ⟨P⟩ := nonempty_actualAnalyticVertexCoefficientData k s t I
  refine ⟨P,?_⟩
  intro hcosupp
  let n := (k+s)+t
  let J := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  let B : ActualMonicVertexFamily MonomialOrder.degLex J :=
    { series := fun a => actualUnshiftedTaylorAlgHom n (P.generator a)
      mem := fun a => Ideal.mem_map_of_mem _ (P.member a)
      monic := P.monic
      lower := fun a β hβ => coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex _
        (P.nonzero a) β (by rwa [P.initial a]) }
  have hB (a : actualInitialVertices MonomialOrder.degLex J) :
      familyVertexSeries MonomialOrder.degLex J B a ∈
        actualFormalCoordinateIdeal n (actualCoefficientCentreVariables k s t) ^
          actualCoefficientCentreVertexWeight k s t a.val :=
    mem_actualPresentationCentre_power_of_local_coefficient_cosupport k s t _ _
      P.domain P.isOpen_domain P.zero_mem_domain (P.coefficient a) (P.holomorphic a)
      (fun γ => actualPrincipalCoefficientIdeal (k+s) (P.coefficient a γ))
      (P.coherent a) (P.coefficient_member a) (hcosupp a) (fun γ _ => P.coefficient_eq a γ)
  have hV := actualReducedVertexSeries_mem_coordinate_power_of_family MonomialOrder.degLex J B
    (actualCoefficientCentreVariables k s t) hB
  refine ⟨hV,?_⟩
  intro e he b
  exact exists_actual_analytic_normalized_member_generators n I (actualCoefficientCentreVariables k s t) e he b hV

end
end Hironaka.HironakaActualAnalyticVertexCoefficientData
