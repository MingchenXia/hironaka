import Hironaka.Resolution.HironakaChowPresentationIndependentFlattener
import Hironaka.Resolution.HironakaChowAnalyticPullbackCoefficientIdeal

/-! Nonzero original-fibre torsion from a principal original coefficient ideal.
All supported division/intersection/maximal-ideal data are derived from the
actual reassembly; no torsion or desired fibre-decrease witness is assumed.
Blueprint first: `hironaka-g10-principal-flattener-torsion.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Pointwise

namespace Hironaka.HironakaChowPrincipalFlattenerTorsion
noncomputable section
open HolGerm HironakaRelativeNormalIdeal
  HironakaHolomorphicJetChartInvariance
  HironakaActualRelativeCoefficientGerms HironakaActualSplitAnalyticCoefficients
  HironakaChowOriginalFibreSupportedDivision HironakaChowFibreLiftUniformTails
  HironakaChowFibreSupportModules HironakaChowFibreDivisionRemainder
  HironakaChowNormalSupportProjection HironakaChowNormalSupportBaseChange
  HironakaChowBaseIdealNormalCoefficients HironakaChowOriginalFlattenerCoefficients
  HironakaChowSameDivisionQuotientFlatness HironakaChowPresentationIndependentFlattener
  HironakaActualAnalyticBaseChangeCoefficients HironakaChowAnalyticPullbackCoefficientIdeal

variable (d t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

private theorem supported_coefficient_mem
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (b : Ideal (HolGerm (ComplexModel d))) (n : fibreRemainderModule d t I)
    (hn : n ∈ b • (⊤ : Submodule (HolGerm (ComplexModel d)) (fibreRemainderModule d t I)))
    (γ : Fin t →₀ ℕ) : actualNormalAnalyticCoefficientGerm d t n.val γ ∈ b := by
  let Δ := assignedRemainderNormalMask (fibreHeadWords d t I)
  have h : n ∈ (b • (⊤ : Submodule (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+t))))).comap (normalSupportSubmodule d t Δ).subtype := by
    rw [normal_support_comap_base_ideal]
    exact hn
  change n.val ∈ b • (⊤ : Submodule (HolGerm (ComplexModel d))
    (HolGerm (ComplexModel (d+t)))) at h
  rw [Ideal.smul_top_eq_map] at h
  exact (mem_extended_base_ideal_iff_all_normal_coefficients d t b n.val).mp h γ

private theorem exists_supported_normalized_remainder
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (a : HolGerm (ComplexModel d)) (ha : a ≠ 0)
    (hp : coefficientIdeal d t I e = Ideal.span {a}) :
    ∃ n : fibreRemainderModule d t I,
      a • n ∈ idealRemainder d t I e ∧
      n ∉ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) •
        (⊤ : Submodule (HolGerm (ComplexModel d)) (fibreRemainderModule d t I)) := by
  let A := HolGerm (ComplexModel d)
  let N := fibreRemainderModule d t I
  let m := IsLocalRing.maximalIdeal A
  have hK : idealRemainder d t I e ≤ (Ideal.span {a}) • (⊤ : Submodule A N) :=
    (coefficientIdeal_le_iff d t I e (Ideal.span {a})).mp hp.le
  by_contra hNo
  push Not at hNo
  have hSmall : coefficientIdeal d t I e ≤ (Ideal.span {a}) • m := by
    apply Ideal.span_le.mpr
    rintro c ⟨i,hi,γ,rfl⟩
    have hr : divisionRemainder d t I e i ∈ (Ideal.span {a}) • (⊤ : Submodule A N) :=
      hK ⟨i,hi,rfl⟩
    rw [Submodule.ideal_span_singleton_smul] at hr
    obtain ⟨n,_,hn⟩ := (Submodule.mem_smul_pointwise_iff_exists _ a (⊤ : Submodule A N)).mp hr
    have hnK : a • n ∈ idealRemainder d t I e := hn ▸ ⟨i,hi,rfl⟩
    have hnM : n ∈ m • (⊤ : Submodule A N) := hNo n hnK
    have hc := supported_coefficient_mem d t I m n hnM γ
    rw [← hn]
    change actualNormalAnalyticCoefficientGerm d t (tangentPullback d t a * n.val) γ ∈ _
    rw [actualNormalAnalyticCoefficientGerm_tangent_mul]
    rw [Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mem_pointwise_smul _ a m hc
  have haP : a ∈ coefficientIdeal d t I e := hp ▸ Ideal.subset_span (by simp)
  have haM := hSmall haP
  rw [Submodule.ideal_span_singleton_smul] at haM
  obtain ⟨b,hb,hEq⟩ := (Submodule.mem_smul_pointwise_iff_exists a a m).mp haM
  change a*b=a at hEq
  have hb1 : b=1 := mul_left_cancel₀ ha (hEq.trans (mul_one a).symm)
  have hOne : (1 : A) ∈ m := hb1 ▸ hb
  have hZero := (HolGerm.mem_maximalIdeal_iff (1 : A)).mp hOne
  simp at hZero

/-- A nonzero actual principal flattener generator produces a real torsion
class whose image in the ENTIRE ORIGINAL closed fibre is nonzero. -/
theorem exists_original_fibre_torsion
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z)
    (a : HolGerm (ComplexModel d)) (ha : a ≠ 0)
    (hp : coefficientIdeal d t I e = Ideal.span {a}) :
    ∃ h : HolGerm (ComplexModel (d+t)),
      Ideal.Quotient.mk I (tangentPullback d t a * h) = 0 ∧
      Ideal.Quotient.mk (I ⊔ Ideal.map (tangentPullback d t).toRingHom
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)))) h ≠ 0 := by
  let A := HolGerm (ComplexModel d)
  let S := HolGerm (ComplexModel (d+t))
  let N := fibreRemainderModule d t I
  let m := IsLocalRing.maximalIdeal A
  let R := divisionRemainder d t I e
  let mN := m • (⊤ : Submodule A N)
  obtain ⟨n,hnK,hnM⟩ := exists_supported_normalized_remainder d t I e a ha hp
  refine ⟨n.val,?_,?_⟩
  · apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [idealRemainder_eq_intersection d t I P e he] at hnK
    exact hnK
  · intro hZero
    have hnFull := Ideal.Quotient.eq_zero_iff_mem.mp hZero
    obtain ⟨i,hi,v,hv,hiv⟩ := Submodule.mem_sup.mp hnFull
    have hRi : R i ∈ mN := idealRemainder_le_maximal d t I P e he ⟨i,hi,rfl⟩
    have hv' : v ∈ m • (⊤ : Submodule A S) := by
      rw [Ideal.smul_top_eq_map]
      exact hv
    have hRv : R v ∈ mN := by
      have hMap := Submodule.mem_map_of_mem (f := R) hv'
      rw [Submodule.map_smul''] at hMap
      have hLe : m • (⊤ : Submodule A S).map R ≤ mN := smul_mono_right m le_top
      exact hLe hMap
    apply hnM
    have hRn : R (i+v) = n := by
      rw [hiv]
      exact remainder_retract d t I P e he n
    rw [← hRn,map_add]
    exact mN.add_mem hRi hRv

/-- Original I and an actual pointed analytic base map internally choose
all target division data before constructing the original-fibre witness. -/
theorem exists_analytic_base_changed_fibre_torsion (b : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (φ : ComplexModel b → ComplexModel d)
    (hφ : ∀ᶠ v in nhds (0 : ComplexModel b), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
    (a : HolGerm (ComplexModel b)) (ha : a ≠ 0)
    (hp : Ideal.map (compAlgHom φ hφ hφ0).toRingHom (canonicalFlattenerIdeal d t I) =
      Ideal.span {a}) :
    let IB := Ideal.map (jointBasePullback d b t φ hφ hφ0).toRingHom I
    ∃ h : HolGerm (ComplexModel (b+t)),
      Ideal.Quotient.mk IB (tangentPullback b t a * h) = 0 ∧
      Ideal.Quotient.mk (IB ⊔ Ideal.map (tangentPullback b t).toRingHom
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel b)))) h ≠ 0 := by
  obtain ⟨P,e,he,_hFG,_hFlat⟩ := exists_original_quotient_flattening_ideal d t I
  rw [canonicalFlattenerIdeal_eq_coefficientIdeal d t I P e he] at hp
  obtain ⟨PB,eB,_hFib,_hWeight,_hBound,_hLift,hEB,_hRnat,_hImage,hCoeff⟩ :=
    exists_base_changed_coefficient_ideal d b t I P e he φ hφ hφ0
  exact exists_original_fibre_torsion b t _ PB eB hEB a ha (hCoeff.trans hp)

end
end Hironaka.HironakaChowPrincipalFlattenerTorsion
