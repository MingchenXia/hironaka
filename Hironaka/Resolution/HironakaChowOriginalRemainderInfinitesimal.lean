import Hironaka.Resolution.HironakaChowFibreDivisionRemainder
import Hironaka.Resolution.HironakaChowFibreRemainderBaseIdeal
import Hironaka.Resolution.HironakaChowNormalSupportBaseChange

/-! ORIGINAL I alone produces SAME native analytic remainder K=R(I),
exactly I∩N, and DERIVES K⊂m_AN geometrically from the actual fibre diagram.
SAME P/e/R/native quotient retained; no infinitesimal certificate input. -/
set_option autoImplicit false
namespace Hironaka.HironakaChowOriginalRemainderInfinitesimal
noncomputable section
open Set Classical HolGerm HironakaRelativeNormalIdeal
  HironakaRelativeNormalFibreHilbertSamuel HironakaChowFibreLiftUniformTails
  HironakaChowOriginalFibreSupportedDivision HironakaChowFibreSupportModules
  HironakaChowFibreDivisionRemainder HironakaChowFibreRemainderBaseIdeal
  HironakaChowNormalSupportProjection HironakaChowNormalSupportBaseChange

variable (d t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

private theorem remainder_mem_original_ideal (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z)
    (g : HolGerm (ComplexModel (d+t))) (hg : g ∈ I) :
    (divisionRemainder d t I e g : HolGerm (ComplexModel (d+t))) ∈ I := by
  have hEq := he (e.symm g)
  rw [e.apply_symm_apply] at hEq
  change g = (∑ j, ((e.symm g).1 j : HolGerm (ComplexModel (d+t))) *
    P.lift (fibreEnumeration d t I j)) + ((e.symm g).2 : HolGerm (ComplexModel (d+t))) at hEq
  have hsum : (∑ j, ((e.symm g).1 j : HolGerm (ComplexModel (d+t))) *
      P.lift (fibreEnumeration d t I j)) ∈ I :=
    I.sum_mem fun j _ => I.mul_mem_left _ (P.member_trace (fibreEnumeration d t I j)).1
  have hr : ((e.symm g).2 : HolGerm (ComplexModel (d+t))) =
      g - (∑ j, ((e.symm g).1 j : HolGerm (ComplexModel (d+t))) * P.lift (fibreEnumeration d t I j)) := by
    linear_combination -hEq
  change ((e.symm g).2 : HolGerm (ComplexModel (d+t))) ∈ I
  rw [hr]
  exact I.sub_mem hg hsum

/-- WHOLE original ideal, actual quotient and SAME remainder; infinitesimality is PRODUCED. -/
theorem exists_original_remainder_infinitesimal (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∃ (P : FibreLiftUniformTailData d t I)
      (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t))),
      (∀ z, e z = supportedReassembly d t I P z) ∧
      (∀ n : fibreRemainderModule d t I, divisionRemainder d t I e n = n) ∧
      idealRemainder d t I e = (I.restrictScalars (HolGerm (ComplexModel d))).comap
        (fibreRemainderModule d t I).subtype ∧
      idealRemainder d t I e ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) •
        (⊤ : Submodule (HolGerm (ComplexModel d)) (fibreRemainderModule d t I)) ∧
      Nonempty ((HolGerm (ComplexModel (d+t)) ⧸ I.restrictScalars (HolGerm (ComplexModel d))) ≃ₗ[HolGerm (ComplexModel d)]
        ((fibreRemainderModule d t I) ⧸ idealRemainder d t I e)) := by
  obtain ⟨P,e,he,hr,_hk,hquot⟩ := exists_original_ideal_remainder_quotient d t I
  let R := divisionRemainder d t I e
  let N := fibreRemainderModule d t I
  let Δ := assignedRemainderNormalMask (fibreHeadWords d t I)
  have hK : idealRemainder d t I e = (I.restrictScalars (HolGerm (ComplexModel d))).comap N.subtype := by
    ext n
    change (∃ i, i ∈ I.restrictScalars (HolGerm (ComplexModel d)) ∧ R i = n) ↔ (n : HolGerm (ComplexModel (d+t))) ∈ I
    constructor
    · rintro ⟨i,hi,hiEq⟩
      rw [← hiEq]
      exact remainder_mem_original_ideal d t I P e he i hi
    · intro hn
      exact ⟨(n : HolGerm (ComplexModel (d+t))),hn,hr n⟩
  refine ⟨P,e,he,hr,hK,?_,hquot⟩
  rintro n ⟨i,hi,rfl⟩
  have hMem := remainder_mem_original_ideal d t I P e he i hi
  have hBase := fibre_remainder_mem_base_ideal d t I (R i : HolGerm (ComplexModel (d+t))) hMem (R i).property
  have hNative : R i ∈ (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) •
      (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))))).comap
        (normalSupportSubmodule d t Δ).subtype := by
    change (R i : HolGerm (ComplexModel (d+t))) ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) •
      (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))))
    rw [Ideal.smul_top_eq_map]
    exact hBase
  rw [normal_support_comap_base_ideal] at hNative
  exact hNative

end
end Hironaka.HironakaChowOriginalRemainderInfinitesimal
