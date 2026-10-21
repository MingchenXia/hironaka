import TranscendentalNakamaye.Pending.HironakaActualExceptionalFilteredDivision
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Actual exceptional finite-jet exactness and the literal whole fibre HS profile

Genuine quotient multiplication and projection give the entire jet exact
sequence and rank recurrence. Literal pivot projection and full coefficient
cancellation establish all-order fibre colons internally. ONE original
canonical normalized family is fixed before every current-order bound and
all HS orders, without a source profile identity or a standardness certificate.
Blueprint: `hironaka-actual-exceptional-jet-hs-comparison-extension.tex`.
-/

set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace TranscendentalNakamaye.Pending.HironakaActualExceptionalJetHSComparison
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualFormalCoordinatePowerDivision
  HironakaActualExceptionalFilteredDivision HironakaActualOriginalFormalHSTransfer
variable {n : ℕ}
local notation "R" => MvPowerSeries (Fin n) ℂ
local notation "𝔪" => actualFormalCoordinateIdeal n univ

/-- The actual full complex jet quotient of a whole ideal. -/
abbrev actualIdealJet (I : Ideal R) (q : ℕ) := R ⧸ (I ⊔ 𝔪^q)

private theorem pointIdeal_eq_genuineVariables (n : ℕ) :
    actualFormalCoordinateIdeal n univ=genuineFormalVariables n := by
  simp [actualFormalCoordinateIdeal,genuineFormalVariables]

instance actualIdealJetFinite (I : Ideal R) (q : ℕ) : FiniteDimensional ℂ (actualIdealJet I q) := by
  unfold actualIdealJet
  rw [pointIdeal_eq_genuineVariables]
  exact finiteDimensional_formal_quotient_sup_variables_pow n q I

/-- The genuine multiplication map retains the original full quotient classes. -/
def exceptionalJetMul (I : Ideal R) (e : Fin n) (q : ℕ) :
    actualIdealJet I q →ₗ[ℂ] actualIdealJet I (q+1) :=
  ((I ⊔ 𝔪^q).mapQ (I ⊔ 𝔪^(q+1)) (LinearMap.mulLeft R (MvPowerSeries.X e)) (by
    intro F hF
    obtain ⟨A,hA,B,hB,rfl⟩ := Submodule.mem_sup.mp hF
    change MvPowerSeries.X e*(A+B)∈I ⊔ 𝔪^(q+1)
    rw [mul_add]
    apply (I ⊔ 𝔪^(q+1)).add_mem
    · exact (le_sup_left : I≤_) (I.mul_mem_left _ hA)
    · apply (le_sup_right : 𝔪^(q+1)≤_)
      rw [pow_succ']
      exact Ideal.mul_mem_mul (Ideal.subset_span ⟨e,mem_univ e,rfl⟩) hB)).restrictScalars ℂ

theorem exceptionalJetMul_mk (I : Ideal R) (e : Fin n) (q : ℕ) (F : R) :
    exceptionalJetMul I e q (Ideal.Quotient.mk (I ⊔ 𝔪^q) F)=
      Ideal.Quotient.mk (I ⊔ 𝔪^(q+1)) (MvPowerSeries.X e*F) := rfl

/-- The genuine fibre projection is the literal full-ideal quotient map. -/
def exceptionalJetFibreProjection (I : Ideal R) (e : Fin n) (q : ℕ) :
    actualIdealJet I (q+1) →ₗ[ℂ] actualIdealJet (I ⊔ Ideal.span {MvPowerSeries.X e}) (q+1) :=
  (Ideal.Quotient.factorₐ ℂ (sup_le (le_trans le_sup_left le_sup_left) le_sup_right :
    I ⊔ 𝔪^(q+1)≤(I ⊔ Ideal.span {MvPowerSeries.X e}) ⊔ 𝔪^(q+1))).toLinearMap

theorem exceptionalJetFibreProjection_mk (I : Ideal R) (e : Fin n) (q : ℕ) (F : R) :
    exceptionalJetFibreProjection I e q (Ideal.Quotient.mk (I ⊔ 𝔪^(q+1)) F)=
      Ideal.Quotient.mk ((I ⊔ Ideal.span {MvPowerSeries.X e}) ⊔ 𝔪^(q+1)) F := rfl

theorem exceptionalJetFibreProjection_surjective (I : Ideal R) (e : Fin n) (q : ℕ) :
    Function.Surjective (exceptionalJetFibreProjection I e q) :=
  Ideal.Quotient.factor_surjective (sup_le (le_trans le_sup_left le_sup_left) le_sup_right :
    I ⊔ 𝔪^(q+1)≤(I ⊔ Ideal.span {MvPowerSeries.X e}) ⊔ 𝔪^(q+1))

/-- The ACTUAL whole colon identity makes multiplication injective. -/
theorem exceptionalJetMul_injective (I : Ideal R) (e : Fin n) (q : ℕ)
    (hCol : (I ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e}=I ⊔ 𝔪^q) :
    Function.Injective (exceptionalJetMul I e q) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro z hz
  obtain ⟨F,rfl⟩ := Ideal.Quotient.mk_surjective z
  change exceptionalJetMul I e q (Ideal.Quotient.mk (I ⊔ 𝔪^q) F)=0 at hz
  rw [exceptionalJetMul_mk] at hz
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hc : F∈(I ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e} := by
    rw [Submodule.mem_colon_singleton]
    simpa only [smul_eq_mul,mul_comm] using hm
  rw [hCol] at hc
  change Ideal.Quotient.mk (I ⊔ 𝔪^q) F=0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hc

/-- The ENTIRE fibre projection kernel equals the ACTUAL multiplication range. -/
theorem exceptionalJetFibreProjection_kernel (I : Ideal R) (e : Fin n) (q : ℕ) :
    LinearMap.ker (exceptionalJetFibreProjection I e q)=LinearMap.range (exceptionalJetMul I e q) := by
  ext z
  obtain ⟨F,rfl⟩ := Ideal.Quotient.mk_surjective z
  constructor
  · intro hz
    change Ideal.Quotient.mk ((I ⊔ Ideal.span {MvPowerSeries.X e}) ⊔ 𝔪^(q+1)) F=0 at hz
    obtain ⟨A,hA,B,hB,rfl⟩ := Submodule.mem_sup.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    obtain ⟨C,hC,D,hD,rfl⟩ := Submodule.mem_sup.mp hA
    obtain ⟨Q,rfl⟩ := Ideal.mem_span_singleton.mp hD
    refine ⟨Ideal.Quotient.mk (I ⊔ 𝔪^q) Q,?_⟩
    rw [exceptionalJetMul_mk]
    apply Ideal.Quotient.eq.mpr
    have hcb : C+B∈I ⊔ 𝔪^(q+1) := (I ⊔ 𝔪^(q+1)).add_mem
      ((le_sup_left : I≤_) hC) ((le_sup_right : 𝔪^(q+1)≤_) hB)
    convert (I ⊔ 𝔪^(q+1)).neg_mem hcb using 1
    ring
  · rintro ⟨z,hz⟩
    obtain ⟨G,rfl⟩ := Ideal.Quotient.mk_surjective z
    change exceptionalJetFibreProjection I e q (Ideal.Quotient.mk (I ⊔ 𝔪^(q+1)) F)=0
    rw [←hz,exceptionalJetMul_mk,exceptionalJetFibreProjection_mk]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (le_trans le_sup_right le_sup_left : Ideal.span {MvPowerSeries.X e}≤_)
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- The genuine finite-jet exact sequence gives its exact complex rank recurrence. -/
theorem exceptionalJetDimension_add (I : Ideal R) (e : Fin n) (q : ℕ)
    (hCol : (I ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e}=I ⊔ 𝔪^q) :
    Module.finrank ℂ (actualIdealJet (I ⊔ Ideal.span {MvPowerSeries.X e}) (q+1))+
      Module.finrank ℂ (actualIdealJet I q)=Module.finrank ℂ (actualIdealJet I (q+1)) := by
  have h := (exceptionalJetFibreProjection I e q).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (exceptionalJetFibreProjection_surjective I e q),finrank_top,
    exceptionalJetFibreProjection_kernel,
    LinearMap.finrank_range_of_inj (f := exceptionalJetMul I e q) (exceptionalJetMul_injective I e q hCol)] at h
  exact h

private theorem pivotProjection_X (e : Fin n) :
    pivotZeroProjection e (MvPowerSeries.X e : R)=0 :=
  (pivotZeroProjection_eq_zero_iff e _).mpr (dvd_refl _)

private theorem X_nonzero (e : Fin n) : (MvPowerSeries.X e : R)≠0 := by
  intro h
  have hh := congrArg (MvPowerSeries.coeff (Finsupp.single e 1)) h
  simp at hh

/-- An actual pivot-fixed whole span has all point-power colon identities. -/
theorem pivot_fixed_span_point_colon_eq {ι : Type*} [Fintype ι]
    (P : ι → R) (e : Fin n) (hP : ∀ i,pivotZeroProjection e (P i)=P i) (q : ℕ) :
    (Ideal.span (range P) ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e}=
      Ideal.span (range P) ⊔ 𝔪^q := by
  let ρ := pivotZeroProjection e
  ext F
  rw [Submodule.mem_colon_singleton]
  change F*MvPowerSeries.X e∈_ ↔ F∈_
  constructor
  · intro hF
    obtain ⟨A,hA,B,hB,hAB⟩ := Submodule.mem_sup.mp hF
    obtain ⟨T,hT⟩ := Ideal.mem_span_range_iff_exists_fun.mp hA
    have hT' : A=∑ i,P i*T i := by simpa only [mul_comm] using hT.symm
    have hproj : ρ A+ρ B=0 := by
      have hh := congrArg ρ hAB
      simpa only [map_add,map_mul,pivotProjection_X,mul_zero,ρ] using hh
    have hker (G : R) : ρ (G-ρ G)=0 := by
      change pivotZeroProjection e (G-pivotZeroProjection e G)=0
      rw [map_sub,pivotZeroProjection_idempotent,sub_self]
    choose C hC using fun i => (pivotZeroProjection_eq_zero_iff e (T i-ρ (T i))).mp (hker (T i))
    obtain ⟨D,hD⟩ := (pivotZeroProjection_eq_zero_iff e (B-ρ B)).mp (hker B)
    have hDq : D∈𝔪^q := by
      apply point_power_of_X_mul_mem e q
      rw [←hD]
      exact (𝔪^(q+1)).sub_mem hB (pivotZeroProjection_mem_point_power e _ _ hB)
    dsimp only [ρ] at hC
    have hAsub : A-ρ A=MvPowerSeries.X e*(∑ i,P i*C i) := by
      rw [hT',map_sum]
      dsimp only [ρ]
      simp_rw [map_mul,hP]
      rw [←Finset.sum_sub_distrib]
      simp_rw [←mul_sub, hC]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hprod : MvPowerSeries.X e*F=MvPowerSeries.X e*((∑ i,P i*C i)+D) := by
      linear_combination -hAB+hAsub+hD+hproj
    have hwhole : F=(∑ i,P i*C i)+D := (mul_left_cancel₀ (X_nonzero e)) hprod
    rw [hwhole]
    apply Submodule.mem_sup.mpr
    refine ⟨∑ i,P i*C i,?_,D,hDq,rfl⟩
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_range_self (x := i))
  · intro hF
    obtain ⟨A,hA,B,hB,rfl⟩ := Submodule.mem_sup.mp hF
    rw [add_mul]
    apply (Ideal.span (range P) ⊔ 𝔪^(q+1)).add_mem
    · exact (le_sup_left : Ideal.span (range P)≤_) ((Ideal.span (range P)).mul_mem_right _ hA)
    · apply (le_sup_right : 𝔪^(q+1)≤_)
      rw [pow_succ]
      exact Ideal.mul_mem_mul hB (Ideal.subset_span ⟨e,mem_univ e,rfl⟩)

/-- Original whole generators and their literal pivot shadows agree modulo the pivot ideal. -/
theorem span_add_pivot_eq_shadow_span_add_pivot {ι : Type*}
    (H : ι → R) (e : Fin n) :
    Ideal.span (range H) ⊔ Ideal.span {MvPowerSeries.X e}=
      Ideal.span (range (fun i => pivotZeroProjection e (H i))) ⊔ Ideal.span {MvPowerSeries.X e} := by
  have hdiff (i : ι) : H i-pivotZeroProjection e (H i)∈Ideal.span {MvPowerSeries.X e} := by
    apply Ideal.mem_span_singleton.mpr
    apply (pivotZeroProjection_eq_zero_iff e _).mp
    rw [map_sub,pivotZeroProjection_idempotent,sub_self]
  apply le_antisymm
  · apply sup_le _ le_sup_right
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change H i∈Ideal.span (range (fun i => pivotZeroProjection e (H i))) ⊔ Ideal.span {MvPowerSeries.X e}
    have hd := (le_sup_right : Ideal.span {MvPowerSeries.X e}≤
      Ideal.span (range (fun i => pivotZeroProjection e (H i))) ⊔ Ideal.span {MvPowerSeries.X e}) (hdiff i)
    have hp := (le_sup_left : Ideal.span (range (fun i => pivotZeroProjection e (H i)))≤
      Ideal.span (range (fun i => pivotZeroProjection e (H i))) ⊔ Ideal.span {MvPowerSeries.X e})
      (Ideal.mem_span_range_self (x := i))
    simpa only [sub_add_cancel] using (Ideal.span (range (fun i => pivotZeroProjection e (H i))) ⊔
      Ideal.span {MvPowerSeries.X e}).add_mem hd hp
  · apply sup_le _ le_sup_right
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change pivotZeroProjection e (H i)∈Ideal.span (range H) ⊔ Ideal.span {MvPowerSeries.X e}
    have hd := (le_sup_right : Ideal.span {MvPowerSeries.X e}≤
      Ideal.span (range H) ⊔ Ideal.span {MvPowerSeries.X e}) (hdiff i)
    have hh := (le_sup_left : Ideal.span (range H)≤Ideal.span (range H) ⊔ Ideal.span {MvPowerSeries.X e})
      (Ideal.mem_span_range_self (x := i))
    convert (Ideal.span (range H) ⊔ Ideal.span {MvPowerSeries.X e}).sub_mem hh hd using 1
    ring

private theorem jet_finrank_zero (I : Ideal R) :
    Module.finrank ℂ (actualIdealJet I 0)=0 := by
  change Module.finrank ℂ (R ⧸ (I ⊔ 𝔪^0))=0
  rw [show I ⊔ 𝔪^0=⊤ from by simp]
  exact Module.finrank_zero_of_subsingleton

private theorem jet_finrank_eq_of_colons (I J : Ideal R) (e : Fin n)
    (hI : ∀ q,(I ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e}=I ⊔ 𝔪^q)
    (hJ : ∀ q,(J ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e}=J ⊔ 𝔪^q)
    (hFibre : I ⊔ Ideal.span {MvPowerSeries.X e}=J ⊔ Ideal.span {MvPowerSeries.X e}) :
    ∀ q,Module.finrank ℂ (actualIdealJet I q)=Module.finrank ℂ (actualIdealJet J q) := by
  intro q
  induction q with
  | zero => rw [jet_finrank_zero,jet_finrank_zero]
  | succ q ih =>
    have hi := exceptionalJetDimension_add I e q (hI q)
    have hj := exceptionalJetDimension_add J e q (hJ q)
    rw [hFibre,ih] at hi
    omega

/-- Genuine all-order jet dimensions compare the whole ideal with the literal
whole fibre extension of its SAME actual generators. -/
theorem genuineFormalHilbertSamuelValue_eq_shadow_of_colons {ι : Type*} [Fintype ι]
    (H : ι → R) (e : Fin n)
    (hCol : ∀ q,(Ideal.span (range H) ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e}=
      Ideal.span (range H) ⊔ 𝔪^q) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n (Ideal.span (range H)) ℓ=
      genuineFormalHilbertSamuelValue n (Ideal.span (range (fun i => pivotZeroProjection e (H i)))) ℓ := by
  have h := jet_finrank_eq_of_colons (Ideal.span (range H))
    (Ideal.span (range (fun i => pivotZeroProjection e (H i)))) e hCol
    (fun q => pivot_fixed_span_point_colon_eq (fun i => pivotZeroProjection e (H i)) e
      (fun i => pivotZeroProjection_idempotent e (H i)) q)
    (span_add_pivot_eq_shadow_span_add_pivot H e) (ℓ+1)
  unfold actualIdealJet at h
  rw [pointIdeal_eq_genuineVariables] at h
  exact h

open FirstPass HolGerm HironakaActualOriginalFormalTaylor HironakaActualTaylorFaithfullyFlat
  HironakaActualPointNormalizedSaturation HironakaActualPointTangentCoefficientHSDrop
  HironakaActualOriginalReducedVertexBasis HironakaActualFormalInitialDiagram
  HironakaActualPointDehomogenizedInitial HironakaActualPointExceptionalInitialForm
  HironakaActualReducedFormalStandardBasis HironakaRelativeNormalIdeal
  HironakaRelativeNormalActualBaseJetDimension HironakaActualAnalyticBlowupTaylor
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticStrictGenerators
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicPointJets

/-- Original data choose ONE actual canonical normalized family before ALL
current-order hypotheses and ALL finite HS orders. The whole actual analytic
normalized ideal then has exactly its literal whole fibre-extension profile. -/
theorem exists_original_point_order_retaining_fibre_hs_family
    (J : Ideal (HolGerm (ComplexModel (0+n)))) (j : Fin n) (b : Fin (0+n) → ℂ) :
    ∃ H : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
        (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)),
      (∀ a,(coordinateGerm (j.natAdd 0))^(normalExponentDegree a.val)*H a=
        actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b (originalReducedVertexBasis J a)) ∧
      actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n) (j.natAdd 0) b=Ideal.span (range H) ∧
      ∀ (_hOrder : ∀ a,H a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^(normalExponentDegree a.val))
        (ℓ : ℕ),
        hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n) (j.natAdd 0) b) ℓ=
          genuineFormalHilbertSamuelValue n
            (Ideal.span (range (fun a => pivotZeroProjection j (originalTaylorAlgHom n (H a))))) ℓ := by
  obtain ⟨H,hH,hNamed,hStruct⟩ := exists_original_point_canonical_strict_symbol_family J j b
  refine ⟨H,hH,hNamed,?_⟩
  intro hOrder ℓ
  rw [hilbertSamuelValue_eq_genuine_formal_extension]
  have hm : Ideal.map (originalTaylorAlgHom n).toRingHom
      (actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n) (j.natAdd 0) b)=
      Ideal.span (range (fun a => originalTaylorAlgHom n (H a))) := by
    rw [hNamed,Ideal.map_span,←range_comp]
    rfl
  rw [hm]
  apply genuineFormalHilbertSamuelValue_eq_shadow_of_colons
  intro q
  have hc := (hStruct hOrder).2 q
  rwa [hm] at hc

end
end TranscendentalNakamaye.Pending.HironakaActualExceptionalJetHSComparison
