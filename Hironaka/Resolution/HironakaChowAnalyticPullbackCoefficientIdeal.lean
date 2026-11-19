import Hironaka.Resolution.HironakaChowAnalyticBaseChangeDivision
import Hironaka.Resolution.HironakaChowFibreRemainderAnalyticMultipliers
import Hironaka.Resolution.HironakaChowOriginalFlattenerCoefficients

/-! ENTIRE analytically extended ideal and exact original coefficient-ideal
naturality. The actual SAME target lift data, inverse and all-numerator
remainder naturality are produced internally before WHOLE ideal control.
Blueprint FIRST: hironaka-g10-analytic-pullback-coefficient-ideal.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology
namespace Hironaka.HironakaChowAnalyticPullbackCoefficientIdeal
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaHolomorphicJetChartInvariance
  HironakaActualRelativeCoefficientGerms HironakaChowNormalSupportProjection
  HironakaChowNormalSupportBaseChange HironakaChowBaseIdealNormalCoefficients
  HironakaChowFibreLiftUniformTails HironakaChowOriginalFibreSupportedDivision
  HironakaChowFibreSupportModules HironakaChowFibreDivisionRemainder
  HironakaChowFibreRemainderAnalyticMultipliers HironakaChowOriginalFlattenerCoefficients
  HironakaActualAnalyticBaseChangeCoefficients HironakaChowAnalyticBaseChangeUniformTails
  HironakaChowAnalyticBaseChangeDivision

variable (d t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

/- Literal reuse of the existing ALL-coefficient and support/base-ideal
intersection criteria, with no new separation or analytic division engine. -/
private theorem support_mem_base_iff_coefficients
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (a : Ideal (HolGerm (ComplexModel d))) (n : fibreRemainderModule d t I) :
    n ∈ a • (⊤ : Submodule (HolGerm (ComplexModel d)) (fibreRemainderModule d t I)) ↔
      ∀ γ, actualNormalAnalyticCoefficientGerm d t n.val γ ∈ a := by
  let Δ := assignedRemainderNormalMask (fibreHeadWords d t I)
  change n ∈ a • (⊤ : Submodule (HolGerm (ComplexModel d)) (normalSupportSubmodule d t Δ)) ↔ _
  rw [← normal_support_comap_base_ideal d t Δ a]
  change (n : HolGerm (ComplexModel (d+t))) ∈ a •
    (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t)))) ↔ _
  rw [Ideal.smul_top_eq_map]
  exact mem_extended_base_ideal_iff_all_normal_coefficients d t a n.val

private theorem jointBasePullback_normalExponentMonomial (d e t : ℕ)
    (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in nhds (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
    (γ : Fin t →₀ ℕ) :
    jointBasePullback d e t φ hφ hφ0 (normalExponentMonomial d t γ) =
      normalExponentMonomial e t γ := by
  simp only [normalExponentMonomial,map_prod,map_pow,jointBasePullback_normalCoordinate]

/-- Actual SAME base-changed division controls the WHOLE extended ideal and
has EXACTLY the original coefficient ideal's actual analytic pullback. -/
theorem exists_base_changed_coefficient_ideal (d e t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : FibreLiftUniformTailData d t I)
    (eA : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (hEA : ∀ z, eA z = supportedReassembly d t I P z)
    (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in nhds (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0) :
    let IB := Ideal.map (jointBasePullback d e t φ hφ hφ0).toRingHom I
    let hJ := base_changed_fibre_ideal_eq d e t I φ hφ hφ0
    ∃ (PB : FibreLiftUniformTailData e t IB)
      (eB : fibreDivisionModule e t IB ≃ₗ[HolGerm (ComplexModel e)] HolGerm (ComplexModel (e+t))),
      PB.fibre = transportFibreData hJ P.fibre ∧ PB.baseWeight = P.baseWeight ∧ PB.bound = P.bound ∧
      (∀ a, PB.lift a = jointBasePullback d e t φ hφ hφ0 (P.lift (fibreVertexEquiv hJ a))) ∧
      (∀ z, eB z = supportedReassembly e t IB PB z) ∧
      (∀ g : HolGerm (ComplexModel (d+t)),
        (divisionRemainder e t IB eB (jointBasePullback d e t φ hφ hφ0 g) : HolGerm (ComplexModel (e+t))) =
          jointBasePullback d e t φ hφ hφ0 (divisionRemainder d t I eA g : HolGerm (ComplexModel (d+t)))) ∧
      idealRemainder e t IB eB ≤
        (Ideal.map (compAlgHom φ hφ hφ0).toRingHom (coefficientIdeal d t I eA)) •
          (⊤ : Submodule (HolGerm (ComplexModel e)) (fibreRemainderModule e t IB)) ∧
      coefficientIdeal e t IB eB =
        Ideal.map (compAlgHom φ hφ hφ0).toRingHom (coefficientIdeal d t I eA) := by
  let IB := Ideal.map (jointBasePullback d e t φ hφ hφ0).toRingHom I
  let σ := jointBasePullback d e t φ hφ hφ0
  let τ := compAlgHom φ hφ hφ0
  let pA := coefficientIdeal d t I eA
  let a := Ideal.map τ.toRingHom pA
  obtain ⟨PB,eB,hFib,hWeight,hBound,hLift,hEB,hRnat⟩ :=
    exists_same_base_changed_linear_division d e t I P eA hEA φ hφ hφ0
  let R := divisionRemainder e t IB eB
  let aN := a • (⊤ : Submodule (HolGerm (ComplexModel e)) (fibreRemainderModule e t IB))
  have hCoeff (g : HolGerm (ComplexModel (d+t))) (γ : Fin t →₀ ℕ) :
      actualNormalAnalyticCoefficientGerm e t (R (σ g) : HolGerm (ComplexModel (e+t))) γ =
        τ (actualNormalAnalyticCoefficientGerm d t
          (divisionRemainder d t I eA g : HolGerm (ComplexModel (d+t))) γ) := by
    rw [hRnat g,actualNormalAnalyticCoefficientGerm_jointBasePullback]
  have hMonomial (i : HolGerm (ComplexModel (d+t))) (hi : i ∈ I) (γ : Fin t →₀ ℕ) :
      R (normalExponentMonomial e t γ * σ i) ∈ aN := by
    apply (support_mem_base_iff_coefficients e t IB a _).mpr
    intro δ
    have hc := hCoeff (normalExponentMonomial d t γ * i) δ
    have hm : σ (normalExponentMonomial d t γ * i) = normalExponentMonomial e t γ * σ i := by
      rw [map_mul,jointBasePullback_normalExponentMonomial]
    rw [hm] at hc
    rw [hc]
    exact Ideal.mem_map_of_mem τ.toRingHom
      (Ideal.subset_span ⟨_,I.mul_mem_left _ hi,δ,rfl⟩)
  have hAnalytic (i : HolGerm (ComplexModel (d+t))) (hi : i ∈ I)
      (h : HolGerm (ComplexModel (e+t))) : R (h * σ i) ∈ aN :=
    analytic_multiplier_mem_base_ideal e t IB PB eB hEB a (σ i) (hMonomial i hi) h
  have hWhole (g : HolGerm (ComplexModel (e+t))) (hg : g ∈ IB) : R g ∈ aN := by
    have hAll : ∀ h : HolGerm (ComplexModel (e+t)), R (h*g) ∈ aN := by
      change g ∈ Ideal.span (σ.toRingHom '' (I : Set (HolGerm (ComplexModel (d+t))))) at hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨i,hi,rfl⟩ := hx
          exact hAnalytic i hi
      | zero =>
          intro h
          simpa only [mul_zero,map_zero] using aN.zero_mem
      | add x y _ _ hx hy =>
          intro h
          rw [mul_add,map_add]
          exact aN.add_mem (hx h) (hy h)
      | smul c x _ hx =>
          intro h
          change R (h*(c*x)) ∈ aN
          rw [← mul_assoc]
          exact hx (h*c)
    simpa only [one_mul] using hAll 1
  have hImage : idealRemainder e t IB eB ≤ aN := by
    rintro n ⟨g,hg,rfl⟩
    exact hWhole g hg
  have hForward : coefficientIdeal e t IB eB ≤ a :=
    (coefficientIdeal_le_iff e t IB eB a).mpr hImage
  have hReverse : a ≤ coefficientIdeal e t IB eB := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro c ⟨i,hi,γ,rfl⟩
    change τ (actualNormalAnalyticCoefficientGerm d t
      (divisionRemainder d t I eA i : HolGerm (ComplexModel (d+t))) γ) ∈
        coefficientIdeal e t IB eB
    rw [← hCoeff i γ]
    exact Ideal.subset_span ⟨σ i,Ideal.mem_map_of_mem σ.toRingHom hi,γ,rfl⟩
  exact ⟨PB,eB,hFib,hWeight,hBound,hLift,hEB,hRnat,hImage,le_antisymm hForward hReverse⟩

end
end Hironaka.HironakaChowAnalyticPullbackCoefficientIdeal
