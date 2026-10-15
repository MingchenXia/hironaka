/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveAmbientContactBudget

/-! Real NORMALIZED source spans construct actual controlled generators on
the unchanged original record, including original ambient ideals. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualNormalizedControlledPrincipalHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualControlledRelativePrincipal HironakaSharpActualChronologicalStrictStep
  HironakaSharpActualCompositeTotalResidual HironakaSharpOriginalFirstMemberExceptionalFactor
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealWeight RestrictedIdealQuotient
  MonomialPartAlong DivisorExponentAlong NormalCrossings NormalCrossingsComparison InvertibleIdealQuotient IdealWeightPowers
  MarkedIdeals MarkedIdeals.MarkedIdeal
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The actual raw pullback normalization is proved BEFORE genuine quotient
cofactors, so no false ambient/relative principal substitution is made. -/
theorem actual_admissible_geoTransform_relative_principal_of_normalized_source (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hp : ∀ x ∈ M.N,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,
      (restrictOn n M.N M.ideal).mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) M.N (·=f) x g)
    {C : Set X} (hC : M.IsAdmissibleCentre C) {π : Y → X} (hπ : IsBlowupAlong n C π) :
    ∀ y ∈ (M.geoTransform C π).N,∃ c : Y → ℂ,(M.geoTransform C π).ideal.mem y c ∧
      ∀ g,(M.geoTransform C π).ideal.mem y g ↔ HolomorphicAt n g y ∧
        IsInSpanOnAt (n := n) (M.geoTransform C π).N (·=c) y g := by
  have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have hdiv : RestrictLe (BlowupStrictSubmanifold.geoStrictTransform π C M.N)
      (GermIdeal.pullback (m := n) π M.ideal)
      (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) M.d) := by
    have h1 := HadamardBridgeAlong.restrictLe_idealPow_vanishingIdeal_of_subset_cosupport hI hN hC.1
      hC.subset_N hC.2.1
    have h2 := RestrictLeCalculus.restrictLe_pullback hπ.contMDiff
      (W := BlowupStrictSubmanifold.geoStrictTransform π C M.N)
      (fun y hy => BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hy)
      (GermIdealPullbackCalculus.isCoherent_idealPow hIC _) h1
    rwa [BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff hIC] at h2
  have hNewN := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hC.subset_N
  have hNorm := actual_normalized_pullback_restrictOn hN hNewN.1 hI hπ.contMDiff
    (fun y hy => BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hy)
  intro y hy
  obtain ⟨f,hf,hgen⟩ := nextTotal_actual_relative_principal hN hπ hp y hy
  have hTot := geoTransform_zeroMark_ideal_eq_restricted_total
    (⟨M.N,[],restrictOn n M.N M.ideal,0⟩ : MarkedIdeal n X) rfl C π
  change (nextTotalMarked M.N (restrictOn n M.N M.ideal) C π).ideal=_ at hTot
  rw [hTot] at hgen
  change ∀ g,(restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C M.N)
    (GermIdeal.pullback (m := n) π (restrictOn n M.N M.ideal))).mem y g ↔
      HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C M.N) (·=f) y g at hgen
  rw [hNorm] at hgen
  exact exists_actual_relative_principal_colon (isInvertibleAlong_geoStrictTransform hπ M.N M.d) hdiv hy f hf hgen

/-- Genuine ambient SNC gives actual ambient generators, then BOTH restricted
span directions on ANY carrier, including BAD incidence points. -/
theorem original_product_normalized_relative_principal (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hE : IsSNCDivisor n E) :
    ∀ x ∈ W,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,
      (restrictOn n W (originalMemberProduct (n := n) E)).mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) W (·=f) x g := by
  intro x _hx
  obtain ⟨_k,_Φ,_σ,_hsrc,_hW,_hfree,_hinj,_hA,hf,hgen,_hres⟩ :=
    exists_actual_original_member_product_normal_form hn hE
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE) (mem_univ x)
  exact ⟨_,hf,fun g => and_congr_right fun _ => restricted_span_iff_principal hf hgen g⟩

/-- ONLY actual original product geometry supplies every normalized relative
generator along ANY same original TEST, retaining all empty steps and marks. -/
theorem original_product_actual_normalized_principal_history (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (d : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (originalMemberProductMarked W E d) T →
      ∀ y ∈ (geoTransformAlong (originalMemberProductMarked W E d) T).N,
        ∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,
          (restrictOn n (geoTransformAlong (originalMemberProductMarked W E d) T).N
            (geoTransformAlong (originalMemberProductMarked W E d) T).ideal).mem y g ↔
          HolomorphicAt n g y ∧ IsInSpanOnAt (n := n)
            (geoTransformAlong (originalMemberProductMarked W E d) T).N (·=f) y g
  | _, .refl, _ => original_product_normalized_relative_principal hn hE
  | _, .step T C π hπ, hT => by
    let M := originalMemberProductMarked W E d
    let Q := geoTransformAlong M T
    have hw0 : M.IsWellFormed :=
      ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
    have hwQ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hT.1
    have hOld := original_product_actual_normalized_principal_history hn hW hE d T hT.1
    intro y hy
    obtain ⟨f,hfMem,hgen⟩ := actual_admissible_geoTransform_relative_principal_of_normalized_source Q
      hwQ.isClosedSubmanifold_N hwQ.isCoherent hOld hT.2 hπ y hy
    have hf : HolomorphicAt n f y := ((hgen f).mp hfMem).1
    refine ⟨f,hf,fun g => ?_⟩
    constructor
    · intro hg
      refine ⟨hg.1,IsInSpanOnAt.trans (fun a ha => ((hgen a).mp ha).2) hg.2⟩
    · rintro ⟨hg,hspan⟩
      exact ⟨hg,IsInSpanOnAt.mono (S := (·=f)) (T := (Q.geoTransform C π).ideal.mem y)
        (fun a ha => ha ▸ hfMem) hspan⟩

end
end Hironaka.HironakaSharpActualNormalizedControlledPrincipalHistory
