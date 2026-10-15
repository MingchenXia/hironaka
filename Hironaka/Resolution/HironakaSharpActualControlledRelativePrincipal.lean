/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualControlledRelativeSaturation

/-! Genuine actual quotient generators from real source-relative equations,
invertible-along denominator geometry and actual restricted divisibility.
Intrinsic all-boundary residual/modified history decrease remain OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualControlledRelativePrincipal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualControlledRelativeSaturation HironakaSharpActualChronologicalStrictStep
  HironakaSharpOriginalFirstMemberExceptionalFactor RelativePrincipalizationSpan
  RestrictedIdealExtension RestrictedIdealQuotient RestrictedIdealWeight MonomialPartAlong
  InvertibleIdealQuotient IdealWeightPowers
  MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder BlowupStrictSubmanifold
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual denominator cofactors construct the quotient generator BEFORE
real nonzero cancellation proves both full relative-colon directions. -/
theorem exists_actual_relative_principal_colon {N : Set X} {I A : GermIdeal n X}
    (hA : IsInvertibleAlong n N A) (hle : RestrictLe N I A)
    {x : X} (hx : x ∈ N) (f : X → ℂ) (hf : HolomorphicAt n f x)
    (hgen : ∀ g,(restrictOn n N I).mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g) :
    ∃ c : X → ℂ,(colonAlong n N I A).mem x c ∧
      ∀ g,(colonAlong n N I A).mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=c) x g := by
  obtain ⟨U,hU,hxU,q,hqdiff,hnon,hqgen⟩ := hA x hx
  have hq := holomorphicAt_of_mdifferentiableOn hU hqdiff hxU
  have hfI : (restrictOn n N I).mem x f := (hgen f).mpr
    ⟨hf,isInSpanOnAt_eq_iff.mpr ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
  have hfA : IsInSpanOnAt (n := n) N (A.mem x) x f :=
    IsInSpanOnAt.trans (fun s hs => hle x hx s hs) hfI.2
  obtain ⟨c,hc,hfqc⟩ := exists_eventuallyEq_within_mul hU hxU hqgen hfA
  have hcJ : (colonAlong n N I A).mem x c := by
    refine ⟨hc,fun b hb => ?_⟩
    obtain ⟨hbhol,a,ha,hbaq⟩ := isInSpanAt_eq_iff.mp ((hqgen x hxU b).mp hb)
    refine restrictOn_congr (restrictOn_mul_left ha hfI) (hbhol.mul hc) ?_
    filter_upwards [hbaq,hfqc] with y hy hyf hyN
    rw [hy,hyf hyN]
    ring
  refine ⟨c,hcJ,?_⟩
  intro g
  constructor
  · intro hg
    have hqA := (hqgen x hxU q).mpr (isInSpanAt_self rfl hq)
    have hqg := (hgen (q*g)).mp (hg.2 q hqA)
    obtain ⟨a,ha,hqgaf⟩ := isInSpanOnAt_eq_iff.mp hqg.2
    have hcancel : ∀ᶠ y in 𝓝 x,y ∈ N → q y*g y=q y*(a y*c y) := by
      filter_upwards [hqgaf,hfqc] with y hy hyf hyN
      have hh := hy hyN
      change q y*g y=a y*f y at hh
      rw [hh,hyf hyN]
      ring
    have hgc := eventuallyEq_within_of_mul_eventuallyEq_within hU hnon hxU hg.1 (ha.mul hc) hcancel
    exact ⟨hg.1,isInSpanOnAt_eq_iff.mpr ⟨a,ha,hgc⟩⟩
  · rintro ⟨hg,hspan⟩
    obtain ⟨a,ha,hgac⟩ := isInSpanOnAt_eq_iff.mp hspan
    refine ⟨hg,fun b hb => ?_⟩
    have hbhol := ((hqgen x hxU b).mp hb).1
    refine restrictOn_congr (restrictOn_mul_left ha (hcJ.2 b hb)) (hbhol.mul hg) ?_
    filter_upwards [hgac] with y hy hyN
    rw [hy hyN]
    ring

/-- Actual source coherence/admissibility internally prove genuine denominator
inclusion before constructing controlled relative principal generators. -/
theorem actual_admissible_geoTransform_relative_principal (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hp : ∀ x ∈ M.N,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,M.ideal.mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) M.N (·=f) x g)
    {C : Set X} (hC : M.IsAdmissibleCentre C) {π : Y → X} (hπ : IsBlowupAlong n C π) :
    ∀ y ∈ (M.geoTransform C π).N,∃ c : Y → ℂ,(M.geoTransform C π).ideal.mem y c ∧
      ∀ g,(M.geoTransform C π).ideal.mem y g ↔ HolomorphicAt n g y ∧
        IsInSpanOnAt (n := n) (M.geoTransform C π).N (·=c) y g := by
  have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have hdiv : RestrictLe (geoStrictTransform π C M.N) (GermIdeal.pullback (m := n) π M.ideal)
      (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) M.d) := by
    have h1 := HadamardBridgeAlong.restrictLe_idealPow_vanishingIdeal_of_subset_cosupport hI hN hC.1
      hC.subset_N hC.2.1
    have h2 := RestrictLeCalculus.restrictLe_pullback hπ.contMDiff (W := geoStrictTransform π C M.N)
      (fun y hy => geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hy)
      (GermIdealPullbackCalculus.isCoherent_idealPow hIC _) h1
    rwa [BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff hIC] at h2
  intro y hy
  obtain ⟨f,hf,hgen⟩ := nextTotal_actual_relative_principal hN hπ hp y hy
  have hTot := geoTransform_zeroMark_ideal_eq_restricted_total (⟨M.N,[],M.ideal,0⟩ : MarkedIdeal n X) rfl C π
  change (nextTotalMarked M.N M.ideal C π).ideal=_ at hTot
  rw [hTot] at hgen
  exact exists_actual_relative_principal_colon (isInvertibleAlong_geoStrictTransform hπ M.N M.d) hdiv hy f hf hgen

end
end Hironaka.HironakaSharpActualControlledRelativePrincipal
