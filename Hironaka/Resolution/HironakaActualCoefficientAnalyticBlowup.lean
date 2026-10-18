/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor
import Hironaka.Resolution.HironakaActualFiniteCoefficientIdeals

/-! Entire actual analytic centre powers and true exceptional quotients from actual local coefficient cosupport. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCoefficientAnalyticBlowup
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf GermIdealOrder
  HironakaActualCoefficientPresentationCentrePower HironakaActualRelativeCoefficientGerms
  HironakaActualRelativeTaylorCoefficients HironakaRelativeNormalMonomialBasis
  HironakaActualLocalCoefficientStrictGenerators HironakaActualAnalyticFormalNormalPowers
  HironakaActualAnalyticBlowupTaylor HironakaActualFiniteCoefficientIdeals
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaHolomorphicJetMonomialSpan

/-- The true original normal-variable range is exactly the actual tail of the finite coordinates. -/
theorem actualTangentCentreVariables_eq_tail (k t : ℕ) :
    actualTangentCentreVariables k t={i : Fin (k+t) | k ≤ i.val} := by
  ext i
  constructor
  · rintro ⟨j,rfl⟩
    simp
  · intro hi
    change k ≤ i.val at hi
    have hil := i.isLt
    refine ⟨⟨i.val-k,by omega⟩,?_⟩
    apply Fin.ext
    dsimp
    omega

/-- Any actual tail centre contracts its whole formal powers to its entire original analytic powers. -/
theorem mem_analytic_tail_pow_iff_actualTaylor_mem (n k q : ℕ) (hk : k ≤ n)
    (g : HolGerm (ComplexModel n)) :
    g ∈ actualAnalyticCoordinateIdeal {i : Fin n | k ≤ i.val} ^ q ↔
      actualUnshiftedTaylorAlgHom n g ∈
        actualFormalCoordinateIdeal n {i : Fin n | k ≤ i.val} ^ q := by
  obtain ⟨t,rfl⟩ : ∃ t, n=k+t := ⟨n-k,(Nat.add_sub_of_le hk).symm⟩
  rw [← actualTangentCentreVariables_eq_tail,actualAnalyticCoordinateIdeal_normal]
  exact mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow k t q g

/-- The three-block presentation centre is literally the same original tail-coordinate set. -/
theorem actualPresentationCentreVariables_eq_tail (k s t : ℕ) :
    actualPresentationCentreVariables (t := t) (actualTangentCentreVariables k s)=
      {i : Fin ((k+s)+t) | k ≤ i.val} := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [actualPresentationCentreVariables,actualTangentCentreVariables_eq_tail]
  · simp [actualPresentationCentreVariables]
    omega

/-- True original local coefficient cosupport constructs the ENTIRE actual analytic centre power. -/
theorem mem_analyticPresentationCentre_pow_of_local_coefficient_cosupport
    (k s t q : ℕ) (g : HolGerm (ComplexModel ((k+s)+t)))
    (U : Set (ComplexModel (k+s))) (hU : IsOpen U) (h0U : (0 : ComplexModel (k+s)) ∈ U)
    (c : (Fin t →₀ ℕ) → ComplexModel (k+s) → ℂ) (hc : ∀ γ, HolAt (c γ) 0)
    (A : (Fin t →₀ ℕ) → GermIdeal (k+s) (ComplexModel (k+s)))
    (hA : ∀ γ, normalExponentDegree γ < q → HironakaSmoothCentreCoherentDomain.CoherentOn (A γ) U)
    (hmem : ∀ γ, normalExponentDegree γ < q → (A γ).mem 0 (c γ))
    (hcosupp : ∀ γ, normalExponentDegree γ < q → U ∩ complexCoordinatePlane (k+s) k ⊆
      cosupport (k+s) univ (A γ) (q-normalExponentDegree γ))
    (hcoeff : ∀ γ, normalExponentDegree γ < q →
      actualNormalAnalyticCoefficientGerm (k+s) t g γ=HolGerm.mk (c γ) (hc γ)) :
    g ∈ actualAnalyticCoordinateIdeal
      (actualPresentationCentreVariables (t := t) (actualTangentCentreVariables k s)) ^ q := by
  rw [actualPresentationCentreVariables_eq_tail]
  apply (mem_analytic_tail_pow_iff_actualTaylor_mem ((k+s)+t) k q (by omega) g).mpr
  rw [← actualPresentationCentreVariables_eq_tail]
  apply mem_actualPresentationCentre_power_of_local_coefficient_cosupport k s t q
    (actualUnshiftedTaylorAlgHom ((k+s)+t) g) U hU h0U c hc A hA hmem hcosupp
  intro γ hγ
  rw [actualFormalNormalCoefficient_actualTaylor,hcoeff γ hγ]

/-- Finite actual analytic input internally supplies all coefficient ideals BEFORE genuine analytic centre division. -/
theorem exists_actual_finite_coefficient_analytic_blowup (k s t q : ℕ)
    {ι : Type*} [Fintype ι] (g : ι → HolGerm (ComplexModel ((k+s)+t)))
    (e : Fin ((k+s)+t))
    (he : e ∈ actualPresentationCentreVariables (t := t) (actualTangentCentreVariables k s))
    (b : Fin ((k+s)+t) → ℂ) :
    ∃ (U : Set (ComplexModel (k+s))), IsOpen U ∧ (0 : ComplexModel (k+s)) ∈ U ∧
      ∃ (c : ι → (Fin t →₀ ℕ) → ComplexModel (k+s) → ℂ) (hc : ∀ i γ, HolAt (c i γ) 0),
        (∀ i γ, normalExponentDegree γ < q →
          MDifferentiableOn 𝓘(ℂ,ComplexModel (k+s)) 𝓘(ℂ,ℂ) (c i γ) U ∧
          HironakaSmoothCentreCoherentDomain.CoherentOn
            (actualPrincipalCoefficientIdeal (k+s) (c i γ)) U ∧
          (actualPrincipalCoefficientIdeal (k+s) (c i γ)).mem 0 (c i γ)) ∧
        (∀ i γ, actualNormalAnalyticCoefficientGerm (k+s) t (g i) γ=
          HolGerm.mk (c i γ) (hc i γ)) ∧
        ∀ i, (∀ γ, normalExponentDegree γ < q → U ∩ complexCoordinatePlane (k+s) k ⊆
          cosupport (k+s) univ (actualPrincipalCoefficientIdeal (k+s) (c i γ))
            (q-normalExponentDegree γ)) →
          g i ∈ actualAnalyticCoordinateIdeal
            (actualPresentationCentreVariables (t := t) (actualTangentCentreVariables k s))^q ∧
          ∃ G : HolGerm (ComplexModel ((k+s)+t)), (coordinateGerm e)^q*G=
            actualAnalyticBlowupPullback
              (actualPresentationCentreVariables (t := t) (actualTangentCentreVariables k s)) e b (g i) ∧
            (MvPowerSeries.X e)^q*actualUnshiftedTaylorAlgHom ((k+s)+t) G=
              actualFormalBlowup
                (actualPresentationCentreVariables (t := t) (actualTangentCentreVariables k s)) e b
                (actualUnshiftedTaylorAlgHom ((k+s)+t) (g i)) := by
  obtain ⟨U,hU,h0,c,hc,hhol,_htaylor,hstable⟩ :=
    exists_actual_finite_local_coefficient_ideals (k+s) t q g
  have hcoeff (i : ι) (γ : Fin t →₀ ℕ) :
      actualNormalAnalyticCoefficientGerm (k+s) t (g i) γ=HolGerm.mk (c i γ) (hc i γ) :=
    hstable i (normalExponentDegree γ+1) γ (by omega)
  refine ⟨U,hU,h0,c,hc,hhol,hcoeff,?_⟩
  intro i hcosupp
  have ha := mem_analyticPresentationCentre_pow_of_local_coefficient_cosupport k s t q (g i)
    U hU h0 (c i) (hc i) (fun γ => actualPrincipalCoefficientIdeal (k+s) (c i γ))
    (fun γ hγ => (hhol i γ hγ).2.1) (fun γ hγ => (hhol i γ hγ).2.2)
    hcosupp (fun γ _ => hcoeff i γ)
  obtain ⟨G,hG,_hTaylor⟩ := exists_actualAnalyticBlowup_quotient
    (actualPresentationCentreVariables (t := t) (actualTangentCentreVariables k s)) e he b q (g i) ha
  refine ⟨ha,G,hG,?_⟩
  have ht := congrArg (actualUnshiftedTaylorAlgHom ((k+s)+t)) hG
  rw [map_mul,map_pow,actualUnshiftedTaylor_coordinate] at ht
  exact ht.trans (DFunLike.congr_fun (actualTaylor_analyticBlowupPullback
    (actualPresentationCentreVariables (t := t) (actualTangentCentreVariables k s)) e b) (g i))

end
end Hironaka.HironakaActualCoefficientAnalyticBlowup
