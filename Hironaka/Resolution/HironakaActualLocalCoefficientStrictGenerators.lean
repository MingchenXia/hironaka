/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCoefficientReducedStrictGenerators
import Hironaka.Resolution.HironakaSmoothCentreCoherentDomain
import Hironaka.Resolution.HironakaRelativeNormalTaylorCoefficients

/-! Genuine local coefficient cosupport supplies entire reduced formal strict generators.
Only real-open coherence and plane cosupport are required; no global extension is assumed. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualLocalCoefficientStrictGenerators
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSmoothCentreCoherentDomain HolGerm GermIdealOrder IdealWeightPowers OkaRelationSheaf
  HironakaRelativeNormalIdeal HironakaRelativeNormalTaylorCoefficients
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalCoordinatePowerDivision
  HironakaActualCoefficientReducedStrictGenerators HironakaActualFormalInitialDiagram
  HironakaActualReducedFormalStandardBasis HironakaActualFormalStrictGenerators
  HironakaActualFormalBlowupMemberGeneration HolomorphicTaylorTail OrderTaylor
  DerivativeIdeal

/-- Actual local finite generators propagate each original membership inside the real domain. -/
theorem eventually_mem_of_coherentOn {n : ℕ} {A : GermIdeal n (ComplexModel n)}
    {U : Set (ComplexModel n)} (hA : CoherentOn A U) {x : ComplexModel n} (hx : x ∈ U)
    {f : ComplexModel n → ℂ} (hf : A.mem x f) : ∀ᶠ y in 𝓝 x, A.mem y f := by
  obtain ⟨V,hV,hxV,_hVU,N,s,_hs,hgen⟩ := hA x hx
  obtain ⟨hfhol,K,t,a,ht,ha,hsum⟩ := (hgen x hxV f).mp hf
  filter_upwards [hV.mem_nhds hxV,eventually_all.mpr fun i => (ha i).eventually,
    hfhol.eventually,hsum.eventually_nhds] with y hyV hya hyf hysum
  exact (hgen y hyV f).mpr ⟨hyf,K,t,a,ht,hya,hysum⟩

/-- Cosupport ONLY on the actual local plane supplies the whole original normal germ power. -/
theorem mk_mem_normalIdeal_pow_of_local_cosupport (k s q : ℕ)
    (A : GermIdeal (k+s) (ComplexModel (k+s)))
    (U : Set (ComplexModel (k+s))) (hU : IsOpen U) (h0U : (0 : ComplexModel (k+s)) ∈ U)
    (hA : CoherentOn A U)
    (hcosupp : U ∩ complexCoordinatePlane (k+s) k ⊆ cosupport (k+s) univ A q)
    {f : ComplexModel (k+s) → ℂ} (hf : HolAt f 0) (hmem : A.mem 0 f) :
    HolGerm.mk f hf ∈ normalIdeal k s ^ q := by
  apply (mem_normalIdeal_pow_iff_InNormalPow k s q hf).mpr
  apply inNormalPow_of_iterDeriv_eq_zero q (show (0 : ComplexModel (k+s)) ∈
    complexCoordinatePlane (k+s) k from fun _ _ => rfl) hf
  filter_upwards [hU.mem_nhds h0U,eventually_mem_of_coherentOn hA h0U hmem]
    with w hwU hwmem hwplane L hL
  have hp : (idealPow (pointIdeal (k+s) w) q).mem w f :=
    mem_idealPow_of_vanishesToOrderOn_univ ((hcosupp ⟨hwU,hwplane⟩).2 f hwmem)
  let e := complexChartAt (n := k+s) w
  have hw : w ∈ e.val.source := mem_complexChartAt_source w
  have hz := iterChartDeriv_eq_zero_of_mem_idealPow hw hp L hL
  rw [iterChartDeriv_eq_iterDeriv e f L hw] at hz
  simpa [e,complexChartAt,chartAt_self_eq] using hz

/-- Genuine Taylor maps the local-cosupport-produced whole germ power to its actual formal power. -/
theorem originalTaylor_mem_coordinate_power_of_local_cosupport (k s q : ℕ)
    (A : GermIdeal (k+s) (ComplexModel (k+s)))
    (U : Set (ComplexModel (k+s))) (hU : IsOpen U) (h0U : (0 : ComplexModel (k+s)) ∈ U)
    (hA : CoherentOn A U)
    (hcosupp : U ∩ complexCoordinatePlane (k+s) k ⊆ cosupport (k+s) univ A q)
    {f : ComplexModel (k+s) → ℂ} (hf : HolAt f 0) (hmem : A.mem 0 f) :
    actualUnshiftedTaylorAlgHom (k+s) (HolGerm.mk f hf) ∈
      actualFormalCoordinateIdeal (k+s) (actualTangentCentreVariables k s) ^ q := by
  have h := Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom (k+s)).toRingHom
    (mk_mem_normalIdeal_pow_of_local_cosupport k s q A U hU h0U hA hcosupp hf hmem)
  rwa [Ideal.map_pow,map_normalIdeal_originalTaylor] at h

/-- ONLY real-open coherence and original local coefficient cosupport supply the entire formal centre power. -/
theorem mem_actualPresentationCentre_power_of_local_coefficient_cosupport
    (k s t q : ℕ) (F : MvPowerSeries (Fin ((k+s)+t)) ℂ)
    (U : Set (ComplexModel (k+s))) (hU : IsOpen U) (h0U : (0 : ComplexModel (k+s)) ∈ U)
    (c : (Fin t →₀ ℕ) → ComplexModel (k+s) → ℂ) (hc : ∀ γ, HolAt (c γ) 0)
    (A : (Fin t →₀ ℕ) → GermIdeal (k+s) (ComplexModel (k+s)))
    (hA : ∀ γ, actualNormalDegree γ < q → CoherentOn (A γ) U)
    (hmem : ∀ γ, actualNormalDegree γ < q → (A γ).mem 0 (c γ))
    (hcosupp : ∀ γ, actualNormalDegree γ < q → U ∩ complexCoordinatePlane (k+s) k ⊆
      cosupport (k+s) univ (A γ) (q-actualNormalDegree γ))
    (hcoeff : ∀ γ, actualNormalDegree γ < q → actualFormalNormalCoefficient F γ =
      actualUnshiftedTaylorAlgHom (k+s) (HolGerm.mk (c γ) (hc γ))) :
    F ∈ actualFormalCoordinateIdeal ((k+s)+t)
      (actualPresentationCentreVariables (actualTangentCentreVariables k s)) ^ q := by
  apply (mem_actualPresentationCentre_power_iff _ q F).mpr
  intro γ hγ
  rw [hcoeff γ hγ]
  exact originalTaylor_mem_coordinate_power_of_local_cosupport k s _ (A γ)
    U hU h0U (hA γ hγ) (hcosupp γ hγ) (hc γ) (hmem γ hγ)

/-- Concrete original coefficient data on a TRUE open neighbourhood, with no global coherence or output certificate. -/
structure ActualLocalReducedCoefficientPresentation (k s t : ℕ)
    (m : MonomialOrder (Fin ((k+s)+t))) (I : Ideal (MvPowerSeries (Fin ((k+s)+t)) ℂ)) where
  domain : Set (ComplexModel (k+s))
  isOpen_domain : IsOpen domain
  zero_mem_domain : (0 : ComplexModel (k+s)) ∈ domain
  coefficient : actualInitialVertices m I → (Fin t →₀ ℕ) → ComplexModel (k+s) → ℂ
  holomorphic : ∀ a γ, HolAt (coefficient a γ) 0
  ideal : actualInitialVertices m I → (Fin t →₀ ℕ) → GermIdeal (k+s) (ComplexModel (k+s))
  coherent : ∀ (a : actualInitialVertices m I) γ,
    actualNormalDegree γ < actualCoefficientCentreVertexWeight k s t a → CoherentOn (ideal a γ) domain
  member : ∀ (a : actualInitialVertices m I) γ,
    actualNormalDegree γ < actualCoefficientCentreVertexWeight k s t a → (ideal a γ).mem 0 (coefficient a γ)
  centre_cosupport : ∀ (a : actualInitialVertices m I) γ,
    actualNormalDegree γ < actualCoefficientCentreVertexWeight k s t a →
      domain ∩ complexCoordinatePlane (k+s) k ⊆ cosupport (k+s) univ (ideal a γ)
        (actualCoefficientCentreVertexWeight k s t a-actualNormalDegree γ)
  coefficient_eq : ∀ (a : actualInitialVertices m I) γ,
    actualNormalDegree γ < actualCoefficientCentreVertexWeight k s t a →
      actualFormalNormalCoefficient (actualReducedVertexSeries m I a) γ =
        actualUnshiftedTaylorAlgHom (k+s) (HolGerm.mk (coefficient a γ) (holomorphic a γ))

/-- All centre powers are INTERNALLY derived from actual local coefficient data. -/
theorem actualLocalReducedCoefficientPresentation_centre_powers (k s t : ℕ)
    (m : MonomialOrder (Fin ((k+s)+t))) (I : Ideal (MvPowerSeries (Fin ((k+s)+t)) ℂ))
    (P : ActualLocalReducedCoefficientPresentation k s t m I) :
    ∀ a : actualInitialVertices m I, actualReducedVertexSeries m I a ∈
      actualFormalCoordinateIdeal ((k+s)+t) (actualCoefficientCentreVariables k s t) ^
        actualCoefficientCentreVertexWeight k s t a := by
  intro a
  exact mem_actualPresentationCentre_power_of_local_coefficient_cosupport k s t _ _
    P.domain P.isOpen_domain P.zero_mem_domain (P.coefficient a) (P.holomorphic a)
    (P.ideal a) (P.coherent a) (P.member a) (P.centre_cosupport a) (P.coefficient_eq a)

/-- Local original data produce the ENTIRE existing true formal strict ideal and literal product identities. -/
theorem exists_actual_reduced_strict_generators_of_local_coefficients (k s t : ℕ)
    (m : MonomialOrder (Fin ((k+s)+t))) (I : Ideal (MvPowerSeries (Fin ((k+s)+t)) ℂ))
    (P : ActualLocalReducedCoefficientPresentation k s t m I)
    (e : Fin ((k+s)+t)) (he : e ∈ actualCoefficientCentreVariables k s t)
    (b : Fin ((k+s)+t) → ℂ) :
    ∃ G : actualInitialVertices m I → MvPowerSeries (Fin ((k+s)+t)) ℂ,
      actualFormalStrictTransform I (actualCoefficientCentreVariables k s t) e he b = Ideal.span (range G) ∧
      ∀ a : actualInitialVertices m I,
        (MvPowerSeries.X e)^actualCoefficientCentreVertexWeight k s t a * G a =
          actualFormalBlowup (actualCoefficientCentreVariables k s t) e b (actualReducedVertexSeries m I a) := by
  let hB := actualLocalReducedCoefficientPresentation_centre_powers k s t m I P
  let G := actualNormalizedReducedFormalVertex m I (actualCoefficientCentreVariables k s t) e he b hB
  refine ⟨G,actualFormalStrictTransform_eq_reduced_vertex_span m I _ e he b hB,?_⟩
  intro a
  exact actualNormalizedFormalMember_spec _ e he b _ (actualReducedVertexSeries m I a) (hB a)

end
end Hironaka.HironakaActualLocalCoefficientStrictGenerators
