/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Blowup.BlowupDerivativeMaximalOrder
import Hironaka.Resolution.HironakaSharpActualTotalAccumulatedResidual

/-! Actual finite-power controlled colon versus genuine all-power relative
saturation. No original invariant/history decrease is inferred. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualControlledRelativeSaturation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualProductNewExceptionalFactor HironakaSharpActualChronologicalStrictStep
  HironakaSharpOriginalFirstMemberRelativeStrict HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalProductTraceOrder
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  InvertibleIdealQuotient IdealWeightPowers MarkedIdeals MarkedIdeals.MarkedIdeal
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- A TRUE ambient principal denominator tests the actual relative colon by
its SAME actual equation, in BOTH full germ directions. -/
theorem colonAlong_actual_principal_mem_iff (N : Set X) (I A : GermIdeal n X)
    {x : X} (a : X → ℂ) (ha : HolomorphicAt n a x)
    (hA : ∀ b,A.mem x b ↔ IsInSpanAt (n := n) (·=a) x b) (g : X → ℂ) :
    (colonAlong n N I A).mem x g ↔ HolomorphicAt n g x ∧ (restrictOn n N I).mem x (a*g) := by
  constructor
  · rintro ⟨hg,hcolon⟩
    exact ⟨hg,hcolon a ((hA a).mpr (isInSpanAt_self rfl ha))⟩
  · rintro ⟨hg,htest⟩
    refine ⟨hg,fun b hb => ?_⟩
    obtain ⟨hbhol,c,hc,hbc⟩ := isInSpanAt_eq_iff.mp ((hA b).mp hb)
    refine restrictOn_congr (restrictOn_mul_left hc htest) (hbhol.mul hg) ?_
    filter_upwards [hbc] with y hy _hyN
    change b y*g y=c y*(a y*g y)
    rw [hy]
    ring

/-- True finite relative-span substitution proves ACTUAL colon normalization. -/
theorem restrictOn_colonAlong_mem_iff (N : Set X) (I A : GermIdeal n X)
    {x : X} (hA : ∀ a,A.mem x a → HolomorphicAt n a x) (g : X → ℂ) :
    (restrictOn n N (colonAlong n N I A)).mem x g ↔ (colonAlong n N I A).mem x g := by
  constructor
  · rintro ⟨hg,K,s,c,hs,hc,hgs⟩
    refine ⟨hg,fun a ha => ?_⟩
    have hrel : IsInSpanOnAt (n := n) N ((restrictOn n N I).mem x) x (a*g) := by
      refine ⟨K,fun j => a*s j,c,fun j => (hs j).2 a ha,hc,?_⟩
      filter_upwards [hgs] with y hy hyN
      change a y*g y=∑ j,c j y*(a y*s j y)
      rw [hy hyN,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    exact ⟨(hA a ha).mul hg,IsInSpanOnAt.trans (fun b hb => hb.2) hrel⟩
  · intro hg
    exact ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩

/-- Genuine all-power saturation is unchanged by a finite actual divisor colon. -/
theorem relativeExceptionalSaturation_finite_colon_mem_iff (N D : Set X) (I : GermIdeal n X)
    {x : X} (a : X → ℂ) (ha : HolomorphicAt n a x)
    (hD : ∀ b,(vanishingIdeal (n := n) D).mem x b ↔ IsInSpanAt (n := n) (·=a) x b)
    (d : ℕ) (g : X → ℂ) :
    (relativeExceptionalSaturation N (colonAlong n N I (idealPow (vanishingIdeal (n := n) D) d)) D).mem x g ↔
      (relativeExceptionalSaturation N I D).mem x g := by
  let A := vanishingIdeal (n := n) D
  have hpow := idealPow_principal_mem_iff ha hD
  have hhol (e : ℕ) (b : X → ℂ) (hb : (idealPow A e).mem x b) : HolomorphicAt n b x :=
    ((hpow e b).mp hb).1
  constructor
  · rintro ⟨k,hg,hcolon⟩
    have hak := BlowupDerivativeIdeal.holomorphicAt_pow ha k
    have had := BlowupDerivativeIdeal.holomorphicAt_pow ha d
    have hakmem : (idealPow A k).mem x (a^k) := (hpow k _).mpr (isInSpanAt_self rfl hak)
    have hinner := (restrictOn_colonAlong_mem_iff N I (idealPow A d) (hhol d) _).mp (hcolon _ hakmem)
    have htest := (colonAlong_actual_principal_mem_iff N I (idealPow A d) (a^d) had (hpow d) _).mp hinner
    refine ⟨d+k,?_⟩
    apply (colonAlong_actual_principal_mem_iff N I (idealPow A (d+k)) (a^(d+k))
      (BlowupDerivativeIdeal.holomorphicAt_pow ha (d+k)) (hpow (d+k)) g).mpr
    refine ⟨hg,?_⟩
    convert htest.2 using 1
    funext y
    simp only [Pi.mul_apply,Pi.pow_apply,pow_add]
    ring
  · rintro ⟨k,hg,hcolon⟩
    refine ⟨k,hg,fun b hb => ?_⟩
    have hbhol := hhol k b hb
    have htest := restrictOn_mul_left (BlowupDerivativeIdeal.holomorphicAt_pow ha d) (hcolon b hb)
    have hinner := (colonAlong_actual_principal_mem_iff N I (idealPow A d) (a^d)
      (BlowupDerivativeIdeal.holomorphicAt_pow ha d) (hpow d) (b*g)).mpr ⟨hbhol.mul hg,htest⟩
    exact ⟨hinner.1,IsInSpanAt.restrict (isInSpanAt_self hinner hinner.1)⟩

/-- Genuine local blowup equations and true off-divisor units identify the
ENTIRE centre-ideal pullback with the actual NEW vanishing ideal. -/
theorem actual_pullback_centre_ideal_eq_exceptional_vanishing {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) :
    GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)=vanishingIdeal (n := n) (π ⁻¹' C) := by
  ext y g
  by_cases hy : π y ∈ C
  · exact MemberTraceIdealAlong.exceptionalDivisor_mem_iff_vanishingIdeal hπ hy g
  · have hleft := (BlowupDerivativeIdeal.isDerivationGenerator_of_notMem hπ hy).generates y hy g
    have hright : (vanishingIdeal (n := n) (π ⁻¹' C)).mem y g ↔ HolomorphicAt n g y := by
      refine ⟨fun hg => hg.1,fun hg => ⟨hg,?_⟩⟩
      filter_upwards [((hπ.1.1.preimage hπ.contMDiff.continuous).isOpen_compl.mem_nhds hy)] with z hz hzD
      exact False.elim (hz hzD)
    exact hleft.trans ((unit_mem_iff_principal (n := n) (x := y) g).symm.trans hright.symm)

/-- ONLY real blowup geometry constructs the WHOLE original-mark controlled
saturation/raw relative STRICT dictionary, without a comparison certificate. -/
theorem geoTransform_relativeExceptionalSaturation_eq (hn : 0 < n) (M : MarkedIdeal n X)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) :
    relativeExceptionalSaturation (M.geoTransform C π).N (M.geoTransform C π).ideal (π ⁻¹' C)=
      nextRelativeStrict M.N M.ideal C π := by
  have hDsnc := BlowupSNCTransform.isSNCDivisor_preimage_centre hπ
  have hD := actual_pullback_centre_ideal_eq_exceptional_vanishing hπ
  ext y g
  obtain ⟨a,ha,hgen⟩ := exists_originalMember_principal hn hDsnc (by simp : π ⁻¹' C ∈ [π ⁻¹' C]) y
  change (relativeExceptionalSaturation (BlowupStrictSubmanifold.geoStrictTransform π C M.N)
    (colonAlong n (BlowupStrictSubmanifold.geoStrictTransform π C M.N) (GermIdeal.pullback (m := n) π M.ideal)
      (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) M.d)) (π ⁻¹' C)).mem y g ↔ _
  rw [hD]
  exact relativeExceptionalSaturation_finite_colon_mem_iff _ _ _ a ha hgen M.d g

end
end Hironaka.HironakaSharpActualControlledRelativeSaturation
