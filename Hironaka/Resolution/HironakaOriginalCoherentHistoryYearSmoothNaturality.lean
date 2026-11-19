/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCoherentHistoryYearOpenNaturality
import Hironaka.Resolution.HironakaSmoothCentreCoherentDomain
import Hironaka.Resolution.HironakaSmoothSubmersionNonmonomialHistory
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeDifferentialIdeals

/-! WHOLE coherent order/year ideals and ALL FOUR marked fields under genuine
smooth pullback of ANY actual ORIGINAL test history. No canonicality assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCoherentHistoryYearSmoothNaturality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HironakaOriginalCoherentHistoryYearIdeal HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeRestriction HironakaSmoothSubmersionRelativeDifferentialIdeals
  HironakaSmoothSubmersionRelativePartsCompanion HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionCartesianTower
  DerivativeIdealAlong DerivativeIdealAlongCoherent MonomialPartAlong NonmonomialOrderLocal
  RelativePrincipalizationSpan RestrictedIdealExtension IdealWeightPowers HironakaSmoothCentreCoherentDomain
  HironakaSmoothSubmersionBlowupLift HironakaSmoothSubmersionBlowupChoiceGeometry
  HironakaSmoothSubmersionBlowupCartesian
open ResolutionInvariantSpec (IsInvDomain)
variable {n m k : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}

/-- The entire original carrier-order equations, including order ZERO,
commute with the genuine actual submersion. -/
theorem pullback_carrierOrderIdeal {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    {N : Set X} {I : GermIdeal n X} (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent) (q : ℕ) :
    GermIdeal.pullback (m := m) f (carrierOrderIdeal N I q)=
      carrierOrderIdeal (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) q := by
  cases q with
  | zero => exact pullback_vanishingIdeal_submersion hf hN
  | succ q =>
    rw [carrierOrderIdeal,pullback_sumIdeal_dimensions hf.contMDiff
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hN) (isCoherent_iterDerivIdealAlong hI hN q),
      pullback_vanishingIdeal_submersion hf hN,pullback_iterDerivIdealAlong hf I hI N hN q]
    rfl

private theorem actual_nm_coherent (hn : 0 < n) {M : MarkedIdeal n X} (hM : IsInvDomain k M) :
    (nmPart M).IsCoherent :=
  isCoherent_nonmonomialPartAlong hn hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isSNCDivisor hM.isWellFormed.isTransverse hM.isWellFormed.isCoherent hM.isNonzeroAlongAt

/-- The SAME actual whole Nm-order ideal of the actual pulled-back record. -/
theorem pullback_nonmonomialOrderIdeal {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0 < n) (M : MarkedIdeal n X) (hM : IsInvDomain k M) (q : ℕ) :
    GermIdeal.pullback (m := m) f (nonmonomialOrderIdeal M q)=
      nonmonomialOrderIdeal (markedPullback (m := m) f M) q := by
  rw [nonmonomialOrderIdeal,pullback_carrierOrderIdeal hf hM.isWellFormed.isClosedSubmanifold_N (actual_nm_coherent hn hM) q]
  have hNm := pullback_nonmonomialPartAlong hf hn hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isSNCDivisor hM.isWellFormed.isTransverse hM.isWellFormed.isCoherent hM.isNonzeroAlongAt
  change carrierOrderIdeal _ (GermIdeal.pullback (m := m) f (nmPart M)) q=_
  rw [hNm]
  rfl

/-- BOTH true baseline summands pull back as the SAME original marked record. -/
theorem pullback_companionYearBaselineIdeal {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0 < n) (M : MarkedIdeal n X) (hM : IsInvDomain k M) (q : ℕ) :
    GermIdeal.pullback (m := m) f (companionYearBaselineIdeal M q)=
      companionYearBaselineIdeal (markedPullback (m := m) f M) q := by
  rw [companionYearBaselineIdeal,pullback_sumIdeal_dimensions
    (I := carrierOrderIdeal M.N M.ideal M.d) (J := nonmonomialOrderIdeal M q) hf.contMDiff
    (isCoherent_carrierOrderIdeal hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent M.d)
    (isCoherent_carrierOrderIdeal hM.isWellFormed.isClosedSubmanifold_N (actual_nm_coherent hn hM) q),
    pullback_carrierOrderIdeal hf hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent M.d,
    pullback_nonmonomialOrderIdeal hf hn M hM q]
  rfl

private theorem actual_mixed_pullback_comp {n m l : ℕ} {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    [ChartedSpace (ComplexModel l) Z] [IsComplexManifold l Z]
    {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel l) 𝓘(ℂ,ComplexModel m) ∞ g)
    (A : GermIdeal n X) (hA : A.IsCoherent) :
    GermIdeal.pullback (m := l) (f ∘ g) A=
      GermIdeal.pullback (m := l) g (GermIdeal.pullback (m := m) f A) := by
  apply GermIdeal.ext
  funext z v
  apply propext
  constructor
  · intro hv
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_
      (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c,hc,rfl⟩
    have hchol : HolomorphicAt n c (f (g z)) :=
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hA hc
    have hfat : ∀ᶠ y in 𝓝 (g z), ContMDiffAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f y :=
      Eventually.of_forall fun _ => hf.contMDiffAt
    have hcfhol : HolomorphicAt m (c ∘ f) (g z) := hchol.comp_contMDiff hfat
    have hcf : (GermIdeal.pullback (m := m) f A).mem (g z) (c ∘ f) :=
      GermIdeal.mem_pullback_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self ⟨c,hc,rfl⟩ hcfhol)
    exact ⟨c ∘ f,hcf,rfl⟩
  · intro hv
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_
      (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c,hc,rfl⟩
    have hgat : ∀ᶠ y in 𝓝 z,MDifferentiableAt 𝓘(ℂ,ComplexModel l) 𝓘(ℂ,ComplexModel m) g y :=
      Eventually.of_forall fun _ => hg.mdifferentiableAt (by simp)
    refine IsInSpanAt.mono ?_
      (isInSpanAt_comp_eventually_mdifferentiable hgat (GermIdeal.mem_pullback_iff.mp hc))
    rintro u' ⟨σ,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨a,ha,rfl⟩


private theorem actual_smooth_blowup_ideal_square {C : Set D} {π : X → D}
    {ρ : Y → D'} {g : D' → D}
    (hg : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g)
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong m (g ⁻¹' C) ρ)
    (I : GermIdeal n D) (hI : I.IsCoherent) :
    GermIdeal.pullback (m := m) (actualLift hg hπ hρ) (GermIdeal.pullback (m := n) π I)=
      GermIdeal.pullback (m := m) ρ (GermIdeal.pullback (m := m) g I) := by
  rw [←actual_mixed_pullback_comp hπ.contMDiff (actualLift_isSubmersion hg hπ hρ).contMDiff I hI,
    ←actual_mixed_pullback_comp hg.contMDiff hρ.contMDiff I hI,actualLift_proj_comm hg hπ hρ]

/-- WHOLE ideal equality for ANY genuine ORIGINAL test prefix, every order
and year. The actual tower induction retains both reset/increment branches. -/
theorem actual_pullback_companionHistoryYearIdeal {f : Y → X} {g : D' → D}
    {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (hn : 0 < n) (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (q a : ℕ) :
    GermIdeal.pullback (m := m) g (companionHistoryYearIdeal M T q a)=
      companionHistoryYearIdeal (markedPullback (m := m) f M) Q q a := by
  induction h generalizing a with
  | refl hf => exact pullback_companionYearBaselineIdeal hf hn M hM q
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    have ht := (isGeoTestTower_step_iff M T C π hπ).mp hT |>.1
    have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T ht
    have hd' := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM (.step T C π hπ) hT
    let J := geoTransformAlong M T
    let J' := geoTransformAlong M (.step T C π hπ)
    let Jq := nonmonomialOrderIdeal J (q+1)
    have hJq : Jq.IsCoherent := isCoherent_carrierOrderIdeal hd.isWellFormed.isClosedSubmanifold_N
      (actual_nm_coherent hn hd) (q+1)
    have hold := (HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
      h M hM.isWellFormed ht).2
    have hnext : IsActualTowerPullback f (.step Q (g ⁻¹' C) ρ hρ) (.step T C π hπ)
        (actualLift hg hπ hρ) := .step h hg hπ hρ
    have hnew := (HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
      hnext M hM.isWellFormed hT).2
    have hbase := pullback_companionYearBaselineIdeal hnext.isSubmersion hn J' hd' q
    rw [←hnew] at hbase
    have horder := pullback_nonmonomialOrderIdeal hg hn J hd (q+1)
    rw [←hold] at horder
    cases a with
    | zero =>
      change GermIdeal.pullback (m := m) (actualLift hg hπ hρ)
        (sumIdeal (companionYearBaselineIdeal J' q) (GermIdeal.pullback (m := n) π Jq))=
          sumIdeal (companionYearBaselineIdeal (geoTransformAlong (markedPullback (m := m) f M)
            (.step Q (g ⁻¹' C) ρ hρ)) q)
            (GermIdeal.pullback (m := m) ρ
              (nonmonomialOrderIdeal (geoTransformAlong (markedPullback (m := m) f M) Q) (q+1)))
      rw [pullback_sumIdeal_dimensions hnext.isSubmersion.contMDiff
        (isCoherent_companionYearBaselineIdeal hn hd' q)
        (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hJq),hbase]
      exact congrArg (sumIdeal _) ((actual_smooth_blowup_ideal_square hg hπ hρ Jq hJq).trans
        (congrArg (GermIdeal.pullback (m := m) ρ) horder))
    | succ a =>
      have hYear := isCoherent_companionHistoryYearIdeal hn hM T ht q a
      have hy := ih ht a
      change GermIdeal.pullback (m := m) (actualLift hg hπ hρ)
        (sumIdeal (companionYearBaselineIdeal J' q)
          (GermIdeal.pullback (m := n) π (Jq.mul (companionHistoryYearIdeal M T q a))))=
          sumIdeal (companionYearBaselineIdeal (geoTransformAlong (markedPullback (m := m) f M)
            (.step Q (g ⁻¹' C) ρ hρ)) q)
            (GermIdeal.pullback (m := m) ρ
              ((nonmonomialOrderIdeal (geoTransformAlong (markedPullback (m := m) f M) Q) (q+1)).mul
                (companionHistoryYearIdeal (markedPullback (m := m) f M) Q q a)))
      rw [pullback_sumIdeal_dimensions hnext.isSubmersion.contMDiff
        (isCoherent_companionYearBaselineIdeal hn hd' q)
        (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff (isCoherent_mul hJq hYear)),hbase]
      have hprod := HironakaSmoothSubmersionCoefficientIdeals.pullback_mul hg.contMDiff hJq hYear
      rw [horder,hy] at hprod
      exact congrArg (sumIdeal _) ((actual_smooth_blowup_ideal_square hg hπ hρ _ (isCoherent_mul hJq hYear)).trans
        (congrArg (GermIdeal.pullback (m := m) ρ) hprod))

/-- ALL FOUR actual marked fields, with the SAME ordered current boundary
and SAME source history, not merely equivalent zero loci. -/
theorem actual_pullback_companionHistoryYearMarked {f : Y → X} {g : D' → D}
    {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (hn : 0 < n) (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (q a : ℕ) :
    markedPullback (m := m) g (companionHistoryYearMarked M T q a)=
      companionHistoryYearMarked (markedPullback (m := m) f M) Q q a := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact preimage_univ
  · have hrecord := (HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
      h M hM.isWellFormed hT).2
    exact (congrArg (fun J => J.E) hrecord).symm
  · exact actual_pullback_companionHistoryYearIdeal hn h M hM hT q a
  · rfl

/-- ONLY original submersion/domain and ANY genuine original TEST prefix
internally construct ONE actual source history and all whole coherent comparisons. -/
theorem exists_original_test_history_coherent_year_smooth_pullback {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0 < n) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧ Q.length=T.length ∧
      IsInvDomain (k+(m-n)) (markedPullback (m := m) f M) ∧
      IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      geoTransformAlong (markedPullback (m := m) f M) Q=markedPullback (m := m) g (geoTransformAlong M T) ∧
      ∀ q a : ℕ,
        (companionHistoryYearIdeal (markedPullback (m := m) f M) Q q a).IsCoherent ∧
        GermIdeal.pullback (m := m) g (companionHistoryYearIdeal M T q a)=
          companionHistoryYearIdeal (markedPullback (m := m) f M) Q q a ∧
        markedPullback (m := m) g (companionHistoryYearMarked M T q a)=
          companionHistoryYearMarked (markedPullback (m := m) f M) Q q a := by
  obtain ⟨D',Q,g,h⟩ := exists_actual_tower hf T
  obtain ⟨hqt,hrecord⟩ := HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
    h M hM.isWellFormed hT
  refine ⟨D',Q,g,h,h.isSubmersion,h.length_eq,isInvDomain_markedPullback_submersion hf M hM,hqt,hrecord,?_⟩
  intro q a
  have hEq := actual_pullback_companionHistoryYearIdeal hn h M hM hT q a
  have hc := GermIdealPullbackCalculus.isCoherent_pullback h.isSubmersion.contMDiff
    (isCoherent_companionHistoryYearIdeal hn hM T hT q a)
  rw [hEq] at hc
  exact ⟨hc,hEq,actual_pullback_companionHistoryYearMarked hn h M hM hT q a⟩

end
end Hironaka.HironakaOriginalCoherentHistoryYearSmoothNaturality
