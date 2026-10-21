/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCoefficientControlledTransform
import Hironaka.Resolution.HironakaRelativeNormalNormalPowerSpread
/-!
# One actual coefficient-cosupport domain from genuine centre powers

True original normal powers spread principal cosupport to one real common
neighbourhood for the finite actual coefficient labels. Shrinking only the
domain retains every original generator and coefficient function. Canonical
reduced normal powers construct this family and domain internally, before
all base-pivot controlled coefficient ideal dictionaries.

Blueprint: `hironaka-actual-coefficient-cosupport-spread-extension.tex`.
-/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaActualCoefficientCosupportSpread
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf GermIdealOrder IdealWeightPowers
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalTaylorCoefficients HironakaRelativeNormalNormalPowerSpread
  HironakaActualCoefficientControlledTransform HironakaActualFiniteCoefficientIdeals
  HironakaActualAnalyticFormalNormalPowers HironakaActualAnalyticVertexCoefficientData
  HironakaActualCoefficientPresentationCentrePower HironakaActualWeightedCoefficientCompression
  HironakaActualCoefficientReducedStrictGenerators HironakaActualFormalInitialDiagram
  HironakaActualAnalyticBlowupTaylor HironakaActualLocalCoefficientStrictGenerators
  HironakaActualAnalyticCentreVertexFamily HironakaActualReducedFormalStandardBasis
  HironakaActualFormalCoordinatePowerDivision HironakaActualRelativeTaylorCoefficients
  HolomorphicTaylorTail OrderTaylor RelativePrincipalizationSpan
  HironakaHolomorphicJetMonomialSpan HironakaActualRelativeCoefficientGerms

theorem exists_actual_principal_cosupport_open (k s q : ℕ)
    (c : ComplexModel (k+s) → ℂ) (hc : HolAt c 0)
    (hp : HolGerm.mk c hc ∈ normalIdeal k s^q) :
    ∃ U : Set (ComplexModel (k+s)), IsOpen U ∧ (0 : ComplexModel (k+s)) ∈ U ∧
      U ∩ complexCoordinatePlane (k+s) k ⊆
        cosupport (k+s) univ (actualPrincipalCoefficientIdeal (k+s) c) q := by
  have hfun := (mem_normalIdeal_pow_iff_InNormalPow k s q hc).mp hp
  obtain ⟨U,hU,h0,hpow⟩ := exists_actual_recursive_normal_power_open q hfun
  refine ⟨U,hU,h0,?_⟩
  intro a ha
  have hpoint : (idealPow (pointIdeal (k+s) a) q).mem a c := by
    apply mem_idealPow_of_inNormalPow (ψ := id) (q := a) (k := k) rfl
      (Eventually.of_forall fun _ => mdifferentiableAt_id) _ q (hpow a ha.1) EventuallyEq.rfl
    intro i hi
    apply mem_pointIdeal_of_apply_eq_zero
    · exact Eventually.of_forall fun _ => (EuclideanSpace.proj i : ComplexModel (k+s) →L[ℂ] ℂ).differentiableAt.mdifferentiableAt
    · exact ha.2 i hi
  refine ⟨mem_univ a,?_⟩
  intro f hf
  have hfpoint : (idealPow (pointIdeal (k+s) a) q).mem a f := by
    change IsInSpanAt (n := k+s) (fun g => g=c) a f at hf
    apply mem_idealPow_of_isInSpanAt
    exact IsInSpanAt.mono (fun g (hg : g=c) => by simpa only [hg] using hpoint) hf
  exact ⟨f,hfpoint,Eventually.of_forall fun _ _ => rfl⟩

theorem exists_actual_finite_principal_cosupport_open (k s : ℕ) {ι : Type*} [Finite ι]
    (c : ι → ComplexModel (k+s) → ℂ) (hc : ∀ i, HolAt (c i) 0) (q : ι → ℕ)
    (hp : ∀ i, HolGerm.mk (c i) (hc i) ∈ normalIdeal k s^(q i)) :
    ∃ U : Set (ComplexModel (k+s)), IsOpen U ∧ (0 : ComplexModel (k+s)) ∈ U ∧
      ∀ i, U ∩ complexCoordinatePlane (k+s) k ⊆
        cosupport (k+s) univ (actualPrincipalCoefficientIdeal (k+s) (c i)) (q i) := by
  choose U hU h0 hcos using fun i => exists_actual_principal_cosupport_open k s (q i) (c i) (hc i) (hp i)
  refine ⟨⋂ i, U i,isOpen_iInter_of_finite hU,mem_iInter.mpr h0,?_⟩
  intro i a ha
  exact hcos i ⟨mem_iInter.mp ha.1 i,ha.2⟩


local instance (t q : ℕ) : Fintype (normalExponentIndex t q) := normalExponentFintype t q

theorem vertex_coefficient_mem_base_power (k s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((k+s)+t)))) (P : ActualAnalyticVertexCoefficientData k s t I)
    (hP : ∀ a, P.generator a ∈ actualAnalyticCoordinateIdeal (actualCoefficientCentreVariables k s t)^
      actualCoefficientCentreVertexWeight k s t a.val) (i : weightedCoefficientIndex k s t I) :
    vertexCoefficientGerm P i ∈ normalIdeal k s^coefficientWeight i := by
  apply (mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow k s _ _).mpr
  have hF := actualTaylor_mem_coordinateCentre_pow (actualCoefficientCentreVariables k s t)
    (actualCoefficientCentreVertexWeight k s t i.1.val) (P.generator i.1) (hP i.1)
  have hc := (mem_actualPresentationCentre_power_iff (actualTangentCentreVariables k s)
    (actualCoefficientCentreVertexWeight k s t i.1.val) _).mp hF i.2.val i.2.property
  rw [P.coefficient_eq] at hc
  exact hc

theorem exists_actual_vertex_cosupport_shrink (k s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((k+s)+t)))) (P : ActualAnalyticVertexCoefficientData k s t I)
    (hP : ∀ a, P.generator a ∈ actualAnalyticCoordinateIdeal (actualCoefficientCentreVariables k s t)^
      actualCoefficientCentreVertexWeight k s t a.val) :
    ∃ Q : ActualAnalyticVertexCoefficientData k s t I,
      Q.generator=P.generator ∧ Q.coefficient=P.coefficient ∧ Q.domain ⊆ P.domain ∧
      ∀ i : weightedCoefficientIndex k s t I,
        Q.domain ∩ complexCoordinatePlane (k+s) k ⊆
          cosupport (k+s) univ (actualPrincipalCoefficientIdeal (k+s) (Q.coefficient i.1 i.2.val))
            (coefficientWeight i) := by
  obtain ⟨U,hU,h0,hcos⟩ := exists_actual_finite_principal_cosupport_open k s
    (fun i : weightedCoefficientIndex k s t I => P.coefficient i.1 i.2.val)
    (fun i => P.holomorphic i.1 i.2.val) coefficientWeight (vertex_coefficient_mem_base_power k s t I P hP)
  let V := U ∩ P.domain
  have hV : IsOpen V := hU.inter P.isOpen_domain
  have h0V : (0 : ComplexModel (k+s)) ∈ V := ⟨h0,P.zero_mem_domain⟩
  have hVP : V ⊆ P.domain := inter_subset_right
  let Q : ActualAnalyticVertexCoefficientData k s t I := { P with
    domain := V
    isOpen_domain := hV
    zero_mem_domain := h0V
    regular := fun a γ hγ => (P.regular a γ hγ).mono hVP
    coherent := fun a γ hγ => coherentOn_actualPrincipalCoefficientIdeal (k+s) (P.coefficient a γ)
      V hV ((P.regular a γ hγ).mono hVP) }
  refine ⟨Q,rfl,rfl,hVP,?_⟩
  intro i a ha
  exact hcos i ⟨ha.1.1,ha.2⟩

theorem exists_actual_vertex_data_cosupport_of_canonical_powers (k s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((k+s)+t))))
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I),
      actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I) a ∈
          actualFormalCoordinateIdeal ((k+s)+t) (actualCoefficientCentreVariables k s t)^
            actualCoefficientCentreVertexWeight k s t a.val) :
    ∃ P : ActualAnalyticVertexCoefficientData k s t I,
      (∀ a, P.generator a ∈ actualAnalyticCoordinateIdeal (actualCoefficientCentreVariables k s t)^
        actualCoefficientCentreVertexWeight k s t a.val) ∧
      ∀ i : weightedCoefficientIndex k s t I,
        P.domain ∩ complexCoordinatePlane (k+s) k ⊆
          cosupport (k+s) univ (actualPrincipalCoefficientIdeal (k+s) (P.coefficient i.1 i.2.val))
            (coefficientWeight i) := by
  obtain ⟨G,hG,hspan⟩ := exists_actual_analytic_centre_vertex_family ((k+s)+t) I
    (actualCoefficientCentreVariables k s t) hV
  let J := Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I
  let q := ∑ a : actualInitialVertices MonomialOrder.degLex J, actualCoefficientCentreVertexWeight k s t a.val
  have hle (a : actualInitialVertices MonomialOrder.degLex J) :
      actualCoefficientCentreVertexWeight k s t a.val≤q :=
    Finset.single_le_sum (f := fun a : actualInitialVertices MonomialOrder.degLex J =>
      actualCoefficientCentreVertexWeight k s t a.val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  obtain ⟨U,hU,h0,c,hc,hd,hT,_hstable⟩ := exists_actual_finite_local_coefficient_ideals (k+s) t q G
  have hd' (a : actualInitialVertices MonomialOrder.degLex J) (γ : Fin t →₀ ℕ)
      (hγ : actualNormalDegree γ<actualCoefficientCentreVertexWeight k s t a.val) :=
    hd a γ (lt_of_lt_of_le hγ (hle a))
  let P : ActualAnalyticVertexCoefficientData k s t I := {
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
    coefficient_eq := hT }
  have hP : ∀ a, P.generator a ∈ actualAnalyticCoordinateIdeal (actualCoefficientCentreVariables k s t)^
      actualCoefficientCentreVertexWeight k s t a.val := fun a => (hG a).2.1
  obtain ⟨Q,hGen,_hCoeff,_hDomain,hCos⟩ := exists_actual_vertex_cosupport_shrink k s t I P hP
  refine ⟨Q,?_,hCos⟩
  intro a
  rw [hGen]
  exact hP a


theorem exists_actual_controlled_coefficient_ideals_of_canonical_powers (k s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((k+s)+t))))
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I),
      actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I) a ∈
          actualFormalCoordinateIdeal ((k+s)+t) (actualCoefficientCentreVariables k s t)^
            actualCoefficientCentreVertexWeight k s t a.val) :
    ∃ P : ActualAnalyticVertexCoefficientData k s t I,
      (∀ a, P.generator a ∈ actualAnalyticCoordinateIdeal (actualCoefficientCentreVariables k s t)^
        actualCoefficientCentreVertexWeight k s t a.val) ∧
      (∀ i : weightedCoefficientIndex k s t I,
        P.domain ∩ complexCoordinatePlane (k+s) k ⊆
          cosupport (k+s) univ (actualPrincipalCoefficientIdeal (k+s) (P.coefficient i.1 i.2.val))
            (coefficientWeight i)) ∧
      ∀ (e : Fin (k+s)) (_he : e ∈ actualTangentCentreVariables k s) (b : Fin (k+s) → ℂ),
        ∃ H : actualInitialVertices MonomialOrder.degLex
            (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I) → HolGerm (ComplexModel ((k+s)+t)),
          (∀ a, (coordinateGerm (e.castAdd t))^(actualCoefficientCentreVertexWeight k s t a.val)*H a=
            actualAnalyticBlowupPullback
              (actualPresentationCentreVariables (t := t) (actualTangentCentreVariables k s)) (e.castAdd t)
              (coefficientChartParameters (k+s) t b) (P.generator a)) ∧
          (∀ i : weightedCoefficientIndex k s t I,
            (coordinateGerm e)^(coefficientWeight i)*actualNormalAnalyticCoefficientGerm (k+s) t (H i.1) i.2.val=
              actualAnalyticBlowupPullback (actualTangentCentreVariables k s) e b (vertexCoefficientGerm P i)) ∧
          Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables k s) e b).toRingHom
              (weightedCompression coefficientWeight (vertexCoefficientGerm P))=
            Ideal.span {(coordinateGerm e)^weightedCommonMark (coefficientWeight (k := k) (s := s) (t := t) (I := I))}*
              weightedCompression coefficientWeight
                (fun i : weightedCoefficientIndex k s t I => actualNormalAnalyticCoefficientGerm (k+s) t (H i.1) i.2.val) ∧
          (Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables k s) e b).toRingHom
              (weightedCompression coefficientWeight (vertexCoefficientGerm P))).colon
                {(coordinateGerm e)^weightedCommonMark (coefficientWeight (k := k) (s := s) (t := t) (I := I))}=
            weightedCompression coefficientWeight
              (fun i : weightedCoefficientIndex k s t I => actualNormalAnalyticCoefficientGerm (k+s) t (H i.1) i.2.val) := by
  obtain ⟨P,hP,hcos⟩ := exists_actual_vertex_data_cosupport_of_canonical_powers k s t I hV
  exact ⟨P,hP,hcos,fun e he b => exists_actual_vertex_controlled_coefficient_ideals k s t I P hcos e he b⟩

end
end Hironaka.HironakaActualCoefficientCosupportSpread
