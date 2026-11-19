import Hironaka.Resolution.HironakaChowPrincipalFlattenerTorsion

/-! Genuine original-fibre torsion over arbitrary analytic quotient bases.
The quotient ideal is arbitrary, and regularity is used in the actual quotient
ring, with no domain or reducedness assumption on that ring.
Blueprint first: hironaka-g10-quotient-base-flattener-torsion.tex. -/
set_option autoImplicit false

namespace Hironaka.HironakaChowQuotientBaseFlattenerTorsion
noncomputable section
open Set Filter Classical
open scoped Topology Pointwise
open HolGerm HironakaRelativeNormalIdeal
  HironakaHolomorphicJetChartInvariance HironakaActualRelativeCoefficientGerms
  HironakaActualSplitAnalyticCoefficients HironakaChowOriginalFibreSupportedDivision
  HironakaChowFibreLiftUniformTails HironakaChowFibreSupportModules
  HironakaChowFibreDivisionRemainder HironakaChowNormalSupportProjection
  HironakaChowNormalSupportBaseChange HironakaChowBaseIdealNormalCoefficients
  HironakaChowOriginalFlattenerCoefficients HironakaChowSameDivisionQuotientFlatness
  HironakaChowPresentationIndependentFlattener HironakaActualAnalyticBaseChangeCoefficients
  HironakaChowAnalyticPullbackCoefficientIdeal HironakaActualRelativeTaylorCoefficients
  HironakaActualOriginalFormalTaylor HironakaActualAnalyticFormalNormalPowers
  HironakaActualCoefficientPresentationCentrePower

variable (d t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

private theorem normalCoefficient_add (f g : HolGerm (ComplexModel (d+t)))
    (γ : Fin t →₀ ℕ) :
    actualNormalAnalyticCoefficientGerm d t (f+g) γ =
      actualNormalAnalyticCoefficientGerm d t f γ +
        actualNormalAnalyticCoefficientGerm d t g γ := by
  apply actualUnshiftedTaylorAlgHom_injective d
  rw [map_add, ←actualFormalNormalCoefficient_actualTaylor,
    ←actualFormalNormalCoefficient_actualTaylor, ←actualFormalNormalCoefficient_actualTaylor]
  apply MvPowerSeries.ext
  intro β
  change MvPowerSeries.coeff (actualJoinedExponent β γ)
    (actualUnshiftedTaylorAlgHom (d+t) (f+g)) = _
  rw [map_add,map_add]
  rfl

private theorem supported_coefficient_mem
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (q : Ideal (HolGerm (ComplexModel d))) (n : fibreRemainderModule d t I)
    (hn : n ∈ q • (⊤ : Submodule (HolGerm (ComplexModel d)) (fibreRemainderModule d t I)))
    (γ : Fin t →₀ ℕ) :
    actualNormalAnalyticCoefficientGerm d t n.val γ ∈ q := by
  let Δ := assignedRemainderNormalMask (fibreHeadWords d t I)
  have h : n ∈ (q • (⊤ : Submodule (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+t))))).comap (normalSupportSubmodule d t Δ).subtype := by
    rw [normal_support_comap_base_ideal]
    exact hn
  change n.val ∈ q • (⊤ : Submodule (HolGerm (ComplexModel d))
    (HolGerm (ComplexModel (d+t)))) at h
  rw [Ideal.smul_top_eq_map] at h
  exact (mem_extended_base_ideal_iff_all_normal_coefficients d t q n.val).mp h γ

/-- Lifted-submodule normalization, with cancellation only in the actual base quotient. -/
private theorem exists_supported_quotient_normalized_remainder
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (q : Ideal (HolGerm (ComplexModel d))) (a : HolGerm (ComplexModel d))
    (ha : Ideal.Quotient.mk q a ≠ 0) (hreg : IsRegular (Ideal.Quotient.mk q a))
    (hp : Ideal.map (Ideal.Quotient.mk q) (coefficientIdeal d t I e) =
      Ideal.span {Ideal.Quotient.mk q a}) :
    ∃ n : fibreRemainderModule d t I,
      a • n ∈ idealRemainder d t I e ⊔ q • (⊤ : Submodule
        (HolGerm (ComplexModel d)) (fibreRemainderModule d t I)) ∧
      n ∉ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) •
        (⊤ : Submodule (HolGerm (ComplexModel d)) (fibreRemainderModule d t I)) := by
  let A := HolGerm (ComplexModel d)
  let N := fibreRemainderModule d t I
  let p := coefficientIdeal d t I e
  let K := idealRemainder d t I e
  let m := IsLocalRing.maximalIdeal A
  let qN := q • (⊤ : Submodule A N)
  have hqProper : q ≠ ⊤ := by
    intro hTop
    apply ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hTop]
    trivial
  have hqm : q ≤ m := IsLocalRing.le_maximalIdeal hqProper
  have hSpan : Ideal.map (Ideal.Quotient.mk q) (Ideal.span {a}) =
      Ideal.span {Ideal.Quotient.mk q a} := by
    rw [Ideal.map_span,Set.image_singleton]
  have hpLe : p ≤ Ideal.span {a} ⊔ q := by
    intro c hc
    apply Ideal.mem_quotient_iff_mem_sup.mp
    rw [hSpan,←hp]
    exact Ideal.mem_map_of_mem _ hc
  have haP : a ∈ p ⊔ q := by
    apply Ideal.mem_quotient_iff_mem_sup.mp
    rw [hp]
    exact Ideal.subset_span (by simp)
  have hK : K ≤ (Ideal.span {a} ⊔ q) • (⊤ : Submodule A N) :=
    (coefficientIdeal_le_iff d t I e (Ideal.span {a} ⊔ q)).mp hpLe
  by_contra hNo
  push Not at hNo
  have hSmall : p ≤ (Ideal.span {a}) • m ⊔ q := by
    apply Ideal.span_le.mpr
    rintro c ⟨i,hi,γ,rfl⟩
    have hki : divisionRemainder d t I e i ∈ K := ⟨i,hi,rfl⟩
    have hk := hK hki
    rw [Submodule.sup_smul,Submodule.ideal_span_singleton_smul] at hk
    obtain ⟨v,hv,r,hr,hvr⟩ := Submodule.mem_sup.mp hk
    obtain ⟨n,_,hn⟩ := (Submodule.mem_smul_pointwise_iff_exists v a
      (⊤ : Submodule A N)).mp hv
    have hnK : a • n ∈ K ⊔ qN := by
      rw [hn,eq_sub_of_add_eq hvr]
      exact (K ⊔ qN).sub_mem (Submodule.mem_sup_left hki) (Submodule.mem_sup_right hr)
    have hnM : n ∈ m • (⊤ : Submodule A N) := hNo n hnK
    have hcn := supported_coefficient_mem d t I m n hnM γ
    have hcr := supported_coefficient_mem d t I q r hr γ
    have hcv : actualNormalAnalyticCoefficientGerm d t v.val γ ∈ (Ideal.span {a}) • m := by
      rw [←hn]
      change actualNormalAnalyticCoefficientGerm d t (tangentPullback d t a * n.val) γ ∈ _
      rw [actualNormalAnalyticCoefficientGerm_tangent_mul,Submodule.ideal_span_singleton_smul]
      exact Submodule.smul_mem_pointwise_smul _ a m hcn
    have hGerm : v.val+r.val = (divisionRemainder d t I e i).val :=
      congrArg (fun x : N => x.val) hvr
    rw [←hGerm,normalCoefficient_add]
    exact ((Ideal.span {a}) • m ⊔ q).add_mem
      (Submodule.mem_sup_left hcv) (Submodule.mem_sup_right hcr)
  have haSmall : a ∈ (Ideal.span {a}) • m ⊔ q :=
    (sup_le hSmall le_sup_right) haP
  obtain ⟨u,hu,w,hw,huw⟩ := Submodule.mem_sup.mp haSmall
  rw [Submodule.ideal_span_singleton_smul] at hu
  obtain ⟨c,hc,hcu⟩ := (Submodule.mem_smul_pointwise_iff_exists u a m).mp hu
  change a*c=u at hcu
  have hEq : Ideal.Quotient.mk q a * Ideal.Quotient.mk q c = Ideal.Quotient.mk q a := by
    have h := congrArg (Ideal.Quotient.mk q) huw
    rw [←hcu,map_add,map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr hw,add_zero] at h
    exact h
  have hcOne : Ideal.Quotient.mk q c = 1 := hreg.left (hEq.trans (mul_one _).symm)
  have hcq : c-1 ∈ q := Ideal.Quotient.eq_zero_iff_mem.mp (by
    rw [map_sub,map_one,hcOne,sub_self])
  have hOne : (1 : A) ∈ m := by
    have h := m.sub_mem hc (hqm hcq)
    convert h using 1
    ring
  have hZero := (HolGerm.mem_maximalIdeal_iff (1 : A)).mp hOne
  simp at hZero

private theorem exists_same_division_quotient_base_fibre_torsion
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z)
    (q : Ideal (HolGerm (ComplexModel d))) (a : HolGerm (ComplexModel d))
    (ha : Ideal.Quotient.mk q a ≠ 0) (hreg : IsRegular (Ideal.Quotient.mk q a))
    (hp : Ideal.map (Ideal.Quotient.mk q) (coefficientIdeal d t I e) =
      Ideal.span {Ideal.Quotient.mk q a}) :
    ∃ h : HolGerm (ComplexModel (d+t)),
      Ideal.Quotient.mk (I ⊔ Ideal.map (tangentPullback d t).toRingHom q)
        (tangentPullback d t a*h) = 0 ∧
      Ideal.Quotient.mk (I ⊔ Ideal.map (tangentPullback d t).toRingHom
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)))) h ≠ 0 := by
  let A := HolGerm (ComplexModel d)
  let S := HolGerm (ComplexModel (d+t))
  let N := fibreRemainderModule d t I
  let m := IsLocalRing.maximalIdeal A
  let R := divisionRemainder d t I e
  let mN := m • (⊤ : Submodule A N)
  obtain ⟨n,hnK,hnM⟩ := exists_supported_quotient_normalized_remainder d t I e q a ha hreg hp
  refine ⟨n.val,?_,?_⟩
  · apply Ideal.Quotient.eq_zero_iff_mem.mpr
    obtain ⟨k,hk,r,hr,hkr⟩ := Submodule.mem_sup.mp hnK
    rw [idealRemainder_eq_intersection d t I P e he] at hk
    have hrFull : r.val ∈ Ideal.map (tangentPullback d t).toRingHom q := by
      let Δ := assignedRemainderNormalMask (fibreHeadWords d t I)
      have h : r ∈ (q • (⊤ : Submodule A S)).comap
          (normalSupportSubmodule d t Δ).subtype := by
        rw [normal_support_comap_base_ideal]
        exact hr
      change r.val ∈ q • (⊤ : Submodule A S) at h
      rwa [Ideal.smul_top_eq_map] at h
    have hGerm : k.val+r.val = tangentPullback d t a*n.val :=
      congrArg (fun x : N => x.val) hkr
    rw [←hGerm]
    exact (I ⊔ Ideal.map (tangentPullback d t).toRingHom q).add_mem
      (Submodule.mem_sup_left hk) (Submodule.mem_sup_right hrFull)
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
    rw [←hRn,map_add]
    exact mN.add_mem hRi hRv

/-- An actual torsion germ over EVERY analytic quotient target, with its
nonzero image in the entire original closed fibre. No division data is input. -/
theorem exists_analytic_quotient_base_fibre_torsion (b : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (φ : ComplexModel b → ComplexModel d)
    (hφ : ∀ᶠ v in nhds (0 : ComplexModel b), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
    (q : Ideal (HolGerm (ComplexModel b))) (a : HolGerm (ComplexModel b))
    (ha : Ideal.Quotient.mk q a ≠ 0) (hreg : IsRegular (Ideal.Quotient.mk q a))
    (hp : Ideal.map (Ideal.Quotient.mk q)
      (Ideal.map (compAlgHom φ hφ hφ0).toRingHom (canonicalFlattenerIdeal d t I)) =
        Ideal.span {Ideal.Quotient.mk q a}) :
    let IB := Ideal.map (jointBasePullback d b t φ hφ hφ0).toRingHom I
    ∃ h : HolGerm (ComplexModel (b+t)),
      Ideal.Quotient.mk (IB ⊔ Ideal.map (tangentPullback b t).toRingHom q)
        (tangentPullback b t a*h) = 0 ∧
      Ideal.Quotient.mk (IB ⊔ Ideal.map (tangentPullback b t).toRingHom
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel b)))) h ≠ 0 := by
  obtain ⟨P,e,he,_hFG,_hFlat⟩ := exists_original_quotient_flattening_ideal d t I
  rw [canonicalFlattenerIdeal_eq_coefficientIdeal d t I P e he] at hp
  obtain ⟨PB,eB,_hFib,_hWeight,_hBound,_hLift,hEB,_hRnat,_hImage,hCoeff⟩ :=
    exists_base_changed_coefficient_ideal d b t I P e he φ hφ hφ0
  exact exists_same_division_quotient_base_fibre_torsion b t _ PB eB hEB q a ha hreg
    ((congrArg (Ideal.map (Ideal.Quotient.mk q)) hCoeff).trans hp)

end
end Hironaka.HironakaChowQuotientBaseFlattenerTorsion
