import TranscendentalNakamaye.Pending.HironakaActualExceptionalJetHSComparison
import TranscendentalNakamaye.Pending.HironakaActualPointNormalizedBennett

/-!
# Actual finite-jet ranks force exceptional initial regularity

Genuine quotient maps, their entire kernel/range identity and finite
rank-nullity derive each full colon equality from literal same-ring shadow
profile equality. The actual original Bennett chain independently forces
whole analytic axis-profile equality under source/current HS persistence.
The Taylor/axis bridge and all-vertex normalized-order converse remain separate.
Blueprint: `hironaka-actual-exceptional-jet-rigidity-extension.tex`.
-/

set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace TranscendentalNakamaye.Pending.HironakaActualExceptionalJetRigidity
noncomputable section
open HironakaActualFormalCoordinatePowerDivision HironakaActualOriginalFormalHSTransfer
  HironakaActualExceptionalFilteredDivision HironakaActualExceptionalJetHSComparison
variable {n : ℕ}
local notation "R" => MvPowerSeries (Fin n) ℂ
local notation "𝔪" => actualFormalCoordinateIdeal n univ

/-- Actual whole finite-jet ranks make the genuine multiplication kernel zero. -/
theorem exceptionalJetMul_injective_of_dimension_add (I : Ideal R) (e : Fin n) (q : ℕ)
    (hDim : Module.finrank ℂ (actualIdealJet (I ⊔ Ideal.span {MvPowerSeries.X e}) (q+1))+
      Module.finrank ℂ (actualIdealJet I q)=Module.finrank ℂ (actualIdealJet I (q+1))) :
    Function.Injective (exceptionalJetMul I e q) := by
  have hv := (exceptionalJetFibreProjection I e q).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (exceptionalJetFibreProjection_surjective I e q),finrank_top,
    exceptionalJetFibreProjection_kernel] at hv
  have hu := (exceptionalJetMul I e q).finrank_range_add_finrank_ker
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  omega

/-- The ACTUAL quotient map injectivity gives the whole exceptional initial colon law. -/
theorem exceptional_point_colon_eq_of_jetMul_injective (I : Ideal R) (e : Fin n) (q : ℕ)
    (hInj : Function.Injective (exceptionalJetMul I e q)) :
    (I ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e}=I ⊔ 𝔪^q := by
  ext F
  rw [Submodule.mem_colon_singleton]
  change F*MvPowerSeries.X e∈_ ↔ F∈_
  constructor
  · intro hF
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hInj
    rw [map_zero,exceptionalJetMul_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa only [mul_comm] using hF)
  · intro hF
    obtain ⟨A,hA,B,hB,rfl⟩ := Submodule.mem_sup.mp hF
    rw [add_mul]
    apply (I ⊔ 𝔪^(q+1)).add_mem
    · exact (le_sup_left : I≤_) (I.mul_mem_right _ hA)
    · apply (le_sup_right : 𝔪^(q+1)≤_)
      rw [pow_succ]
      exact Ideal.mul_mem_mul hB (Ideal.subset_span ⟨e,mem_univ e,rfl⟩)

private theorem pointIdeal_eq_genuineVariables (n : ℕ) :
    actualFormalCoordinateIdeal n univ=genuineFormalVariables n := by
  simp [actualFormalCoordinateIdeal,genuineFormalVariables]

private theorem jet_rank_of_entire_hs (I J : Ideal R)
    (hHS : ∀ ℓ,genuineFormalHilbertSamuelValue n I ℓ=genuineFormalHilbertSamuelValue n J ℓ) :
    ∀ q,Module.finrank ℂ (actualIdealJet I q)=Module.finrank ℂ (actualIdealJet J q) := by
  intro q
  cases q with
  | zero =>
    change Module.finrank ℂ (R ⧸ (I ⊔ 𝔪^0))=Module.finrank ℂ (R ⧸ (J ⊔ 𝔪^0))
    rw [show I ⊔ 𝔪^0=⊤ from by simp,show J ⊔ 𝔪^0=⊤ from by simp]
  | succ q =>
    unfold actualIdealJet
    rw [pointIdeal_eq_genuineVariables]
    exact hHS q

/-- Equality with the literal SAME-RING shadow profile internally forces every
actual exceptional multiplication and all whole initial-colon identities. -/
theorem exceptional_colons_iff_entire_shadow_hs {ι : Type*} [Fintype ι]
    (H : ι → R) (e : Fin n) :
    (∀ q,(Ideal.span (range H) ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e}=Ideal.span (range H) ⊔ 𝔪^q) ↔
    ∀ ℓ,genuineFormalHilbertSamuelValue n (Ideal.span (range H)) ℓ=
      genuineFormalHilbertSamuelValue n (Ideal.span (range (fun i => pivotZeroProjection e (H i)))) ℓ := by
  constructor
  · exact fun h ℓ => genuineFormalHilbertSamuelValue_eq_shadow_of_colons H e h ℓ
  · intro hHS q
    have hJet := jet_rank_of_entire_hs _ _ hHS
    have hD := exceptionalJetDimension_add (Ideal.span (range (fun i => pivotZeroProjection e (H i)))) e q
      (pivot_fixed_span_point_colon_eq (fun i => pivotZeroProjection e (H i)) e
        (fun i => pivotZeroProjection_idempotent e (H i)) q)
    rw [←span_add_pivot_eq_shadow_span_add_pivot H e,←hJet q,←hJet (q+1)] at hD
    apply exceptional_point_colon_eq_of_jetMul_injective
    exact exceptionalJetMul_injective_of_dimension_add _ e q hD

open FirstPass HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaActualAnalyticStrictGenerators HironakaActualAxisContraction
  HironakaActualAxisSpecializationHS HironakaActualPointInitialIdealInclusion
  HironakaActualPointNormalizedBennett HironakaActualPointUnitCoordinateChange
  HironakaActualUnshiftedInitialHSTransfer HironakaActualCoefficientPresentationCentrePower

/-- Actual source/current all-order persistence internally identifies the
ENTIRE current analytic axis-image profile via the genuine Bennett chain. -/
theorem normalized_entire_hs_eq_axis_of_original_persistence
    (I : Ideal (HolGerm (ComplexModel n))) (e : Fin n) (b : Fin n → ℂ)
    (hPersist : ∀ ℓ,hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I univ e b) ℓ=hilbertSamuelValue I ℓ) :
    ∀ ℓ,hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I univ e b) ℓ=
      hilbertSamuelValue (Ideal.map (actualAxisContractionGerm e 0).toRingHom
        (actualAnalyticNormalizedMemberIdeal I univ e b)) ℓ := by
  intro ℓ
  let N := actualAnalyticNormalizedMemberIdeal I univ e b
  let K := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  let L := Ideal.map (actualAxisContractionGerm e 0).toRingHom N
  let P := actualDehomogenizedInitialIdeal K e b
  have hSub : P≤L := actualDehomogenizedInitialIdeal_le_axis_normalized_image n I e b
  have hLower : hilbertSamuelValue N ℓ≤hilbertSamuelValue L ℓ :=
    hilbertSamuelValue_actual_axis_specialization e N ℓ
  have hMid : hilbertSamuelValue L ℓ≤hilbertSamuelValue P ℓ :=
    @hilbertSamuelValue_antitone_original_ideal n P L hSub ℓ
  have hUnit : hilbertSamuelValue P ℓ=hilbertSamuelValue
      (actualUnshiftedTranslatedInitialIdeal K (actualPointUnitBasePoint e b)) ℓ :=
    hilbertSamuelValue_actualDehomogenizedInitialIdeal_eq_translated K e b ℓ
  have hUpper : hilbertSamuelValue (actualUnshiftedTranslatedInitialIdeal K (actualPointUnitBasePoint e b)) ℓ≤
      hilbertSamuelValue I ℓ := hilbertSamuelValue_actual_original_translated_initial_le n I (actualPointUnitBasePoint e b) ℓ
  change hilbertSamuelValue N ℓ=hilbertSamuelValue L ℓ
  have hp : hilbertSamuelValue N ℓ=hilbertSamuelValue I ℓ := hPersist ℓ
  omega

end
end TranscendentalNakamaye.Pending.HironakaActualExceptionalJetRigidity
