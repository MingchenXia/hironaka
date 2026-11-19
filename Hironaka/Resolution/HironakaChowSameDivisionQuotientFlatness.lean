import Hironaka.Resolution.HironakaChowOriginalFlattenerCoefficients

/-! Quotient-base flatness for ANY SAME actual supported division.
The ordinary I/P/e/he inputs retain the actual reassembly equation; its
retraction, whole remainder intersection and infinitesimality are derived.
Only the existing finite-sum plumbing is repeated, with zero duplicate
mathematical credit. The public native quotient/coefficient/flatness
contracts are reused without reselecting an original division equivalence.
Blueprint first: hironaka-g10-same-division-quotient-flatness.tex. -/
set_option autoImplicit false
namespace Hironaka.HironakaChowSameDivisionQuotientFlatness
noncomputable section
open Set Classical HolGerm HironakaRelativeNormalIdeal
  HironakaChowFibreLiftUniformTails HironakaChowOriginalFibreSupportedDivision
  HironakaChowFibreSupportModules HironakaChowFibreDivisionRemainder
  HironakaChowFibreRemainderBaseIdeal HironakaChowNormalSupportProjection
  HironakaChowNormalSupportBaseChange HironakaChowNormalSupportQuotientFlatness
  HironakaChowOriginalFlattenerCoefficients

variable (d t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

/- Pin the native quotient factories used by the existing actual criterion. -/
local instance (I : Ideal (HolGerm (ComplexModel (d+t))))
    (a : Ideal (HolGerm (ComplexModel d))) :
    Module (HolGerm (ComplexModel d) ⧸ a)
      (normalSupportQuotient d t (assignedRemainderNormalMask (fibreHeadWords d t I)) a) :=
  (Module.isTorsionBySet_quotient_ideal_smul (fibreRemainderModule d t I) a).module

local instance (I : Ideal (HolGerm (ComplexModel (d+t))))
    (a : Ideal (HolGerm (ComplexModel d))) :
    SMul (Ideal (HolGerm (ComplexModel d) ⧸ a))
      (Submodule (HolGerm (ComplexModel d) ⧸ a)
        (normalSupportQuotient d t (assignedRemainderNormalMask (fibreHeadWords d t I)) a)) :=
  Submodule.moduleSubmodule.toSMul

/-- The SAME actual reassembly equation derives the remainder retraction. -/
theorem remainder_retract (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z)
    (n : fibreRemainderModule d t I) : divisionRemainder d t I e n = n := by
  have hn : e (0,n) = (n : HolGerm (ComplexModel (d+t))) := by
    rw [he]
    change (∑ j, (0 : HolGerm (ComplexModel (d+t))) * P.lift (fibreEnumeration d t I j)) +
      (n : HolGerm (ComplexModel (d+t))) = _
    simp only [zero_mul,Finset.sum_const_zero,zero_add]
  have hi := e.symm_apply_apply (0,n)
  rw [hn] at hi
  exact congrArg Prod.snd hi

private theorem reassembly_difference_mem (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z) (g : HolGerm (ComplexModel (d+t))) :
    g - (divisionRemainder d t I e g : HolGerm (ComplexModel (d+t))) ∈ I := by
  have hEq := he (e.symm g)
  rw [e.apply_symm_apply] at hEq
  change g = (∑ j, ((e.symm g).1 j : HolGerm (ComplexModel (d+t))) *
    P.lift (fibreEnumeration d t I j)) + ((e.symm g).2 : HolGerm (ComplexModel (d+t))) at hEq
  change g - ((e.symm g).2 : HolGerm (ComplexModel (d+t))) ∈ I
  rw [sub_eq_iff_eq_add.mpr hEq]
  exact I.sum_mem fun j _ => I.mul_mem_left _ (P.member_trace (fibreEnumeration d t I j)).1

/-- The WHOLE same remainder image is the actual original ideal intersection. -/
theorem idealRemainder_eq_intersection (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z) :
    idealRemainder d t I e = (I.restrictScalars (HolGerm (ComplexModel d))).comap
      (fibreRemainderModule d t I).subtype := by
  ext n
  change (∃ i, i ∈ I.restrictScalars (HolGerm (ComplexModel d)) ∧
    divisionRemainder d t I e i = n) ↔ (n : HolGerm (ComplexModel (d+t))) ∈ I
  constructor
  · rintro ⟨i,hi,hiEq⟩
    rw [← hiEq]
    have hd := reassembly_difference_mem d t I P e he i
    simpa only [sub_sub_cancel] using I.sub_mem hi hd
  · intro hn
    exact ⟨(n : HolGerm (ComplexModel (d+t))),hn,remainder_retract d t I P e he n⟩

/-- The actual fibre trace and support intersection derive SAME K ≤ m_A N. -/
theorem idealRemainder_le_maximal (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z) :
    idealRemainder d t I e ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) •
      (⊤ : Submodule (HolGerm (ComplexModel d)) (fibreRemainderModule d t I)) := by
  intro n hn
  rw [idealRemainder_eq_intersection d t I P e he] at hn
  have hMem : (n : HolGerm (ComplexModel (d+t))) ∈ I := hn
  have hBase := fibre_remainder_mem_base_ideal d t I n hMem n.property
  let Δ := assignedRemainderNormalMask (fibreHeadWords d t I)
  have hNative : n ∈ (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) •
      (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))))).comap
        (normalSupportSubmodule d t Δ).subtype := by
    change (n : HolGerm (ComplexModel (d+t))) ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) •
      (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))))
    rw [Ideal.smul_top_eq_map]
    exact hBase
  rw [normal_support_comap_base_ideal] at hNative
  exact hNative

/-- EVERY original base quotient is flat exactly when it kills the coefficient
ideal of THIS SAME actual supported division; no division is reselected. -/
theorem flat_original_quotient_iff (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z)
    (a : Ideal (HolGerm (ComplexModel d))) :
    Module.Flat (HolGerm (ComplexModel d) ⧸ a)
      (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ Ideal.map (tangentPullback d t).toRingHom a)) ↔
      coefficientIdeal d t I e ≤ a := by
  let Δ := assignedRemainderNormalMask (fibreHeadWords d t I)
  let K := idealRemainder d t I e
  have hr := remainder_retract d t I P e he
  have hmin := idealRemainder_le_maximal d t I P e he
  let q := original_quotient_remainder_equiv d t I P e he hr a
  constructor
  · intro hFlat
    let := hFlat
    have hTarget : Module.Flat (HolGerm (ComplexModel d) ⧸ a)
        (normalSupportQuotient d t Δ a ⧸ normalSupportKernelImage d t Δ a K) :=
      Module.Flat.of_linearEquiv q.symm
    exact (coefficientIdeal_le_iff d t I e a).mpr
      ((flat_normalSupportQuotientKernel_iff d t Δ a K hmin).mp hTarget)
  · intro hp
    have hTarget := (flat_normalSupportQuotientKernel_iff d t Δ a K hmin).mpr
      ((coefficientIdeal_le_iff d t I e a).mp hp)
    let := hTarget
    exact Module.Flat.of_linearEquiv q

end
end Hironaka.HironakaChowSameDivisionQuotientFlatness
