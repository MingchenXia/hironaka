/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneRepresentative
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerSplitIso
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.BoundaryCount
import Hironaka.Invariant.CodimOnePartCanonical
import Hironaka.MarkedIdeal.CodimOneSupportAlong
import Hironaka.Invariant.ContactLowerValue
import Hironaka.Invariant.ContactStageKept
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Invariant.MemberRestrictTowerIso
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneAdmissible
import Hironaka.Invariant.StepOneCanonicalTail
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.Invariant.StepOneRegime
import Hironaka.Invariant.StepOneValue
import Hironaka.Invariant.StepOneValueMasked
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1: restriction to open sets (property (5))

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`: the resolution commutes with étale
morphisms, in particular with restriction to open sets.

For `U ⊆ X` open and `𝔍|_U` the restriction, the masked Step 1 values of `𝔍|_U` along `T|_U` are those of `𝔍` along
`T`, and canonical segments restrict. `J̄(𝔍|_U) = J̄(𝔍)|_U` (`ContactStageKept.barMarked_pullback_val`) and
transforms commute with restriction, so the original members, levels, special points (codimension-one part and
member locus under restriction) and regimes are the traces of those of `𝔍`; runs agree
(`NonmonomialOrderRegime.regimeRun_restrict_of`); the split of `T|_U` is the restriction of the split of `T` up to
isomorphisms over `id_U` (`BlowupTowerSplitIso.exists_isTowerIso_split_restrict`); the lower values agree by
`ContactLowerValue.lowerValueL_zero_restrict` (level `0`) and `MemberRestrictTowerIso.lowerValueL_succ_restrict`
(levels `≥ 1`).

## Main results

* `geoTransformAlong_barMarked_restrict`, `restrict_facts`: the marked ideal of Step 1 of `𝔍|_U` along `T|_U`, and the levels,
  special points and regimes;
* `hypotheses_restrict`: the hypotheses of Step 1 pass to `𝔍|_U`;
* `stepOneInvM_restrict_eq`, **`stepOneInvM_restrict`**: property (5).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneRestrictOpen

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime Hironaka.StepOneValue Hironaka.StepOneLowerDomain Hironaka.StepOneValueMasked Hironaka.StepOneCanonicalTail Hironaka.HomogenizedIdealAlong Hironaka.CodimOneSupportAlong Hironaka.MarkedIdealRestrictOpen Hironaka.MemberInterLocusAlong Hironaka.BlowupTowerIsoTail Hironaka.MarkedIdealBiholomorphism
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)

noncomputable section

variable {n : ℕ}

section Restrict

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) (U : Opens X)

/-- **The marked ideal of Step 1 of `𝔍|_U` along `T|_U`** is the restriction of that of `𝔍` along `T` (a multiple test blow-up of
`J̄`). -/
theorem geoTransformAlong_barMarked_restrict (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) :
    geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
        (restrict U T) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong (barMarked 𝔍) T) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  rw [show barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) =
      MarkedIdeal.pullback (Subtype.val : U → X) (barMarked 𝔍) from
    ContactStageKept.barMarked_pullback_val U h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd]
  exact geoTransformAlong_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T hT

/-- **Levels, special points, regimes and the cosupport along `T|_U`** are the traces of those along `T`. -/
theorem restrict_facts (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) :
    IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T) ∧
      (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
        (restrict U T)).cosupp = (Subtype.val : openPreimage T U → Y) ⁻¹' (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
      ∀ p : openPreimage T U,
        level (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p =
            level 𝔍 T p ∧
          (IsSpecial (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p ↔
            IsSpecial 𝔍 T p) ∧
          ∀ s, stepRegime (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) s (restrict U T) p ↔
            stepRegime 𝔍 s T p := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T hT
  have hg := geoTransformAlong_barMarked_restrict 𝔍 U h𝔍 hd T hT
  have htest : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (restrict U T) := by
    rw [show barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) =
        MarkedIdeal.pullback (Subtype.val : U → X) (barMarked 𝔍) from
      ContactStageKept.barMarked_pullback_val U h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd]
    exact isGeoTestTower_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T hT
  have hc : (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (restrict U T)).cosupp = (Subtype.val : openPreimage T U → Y) ⁻¹' (geoTransformAlong (barMarked 𝔍) T).cosupp := by
    rw [hg]
    exact cosupp_pullback_val _ (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) _
  have hO := ContactLowerValue.origMembers_restrict U 𝔍 h𝔍 hd hT
  refine ⟨htest, hc, fun p => ?_⟩
  have hl : level (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p =
      level 𝔍 T p := by
    unfold level
    rw [hO]
    exact CodimOnePartCanonical.boundaryCount_map_preimage _ _ p
  have hs : IsSpecial (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p ↔
      IsSpecial 𝔍 T p := by
    have hcod := CodimOnePartCanonical.codimOnePartAlong_pullback_val (openPreimage T U)
      (𝔞 := (geoTransformAlong (barMarked 𝔍) T).ideal)
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg)
      (N := (geoTransformAlong (barMarked 𝔍) T).N) (geoTransformAlong (barMarked 𝔍) T).d
    have hmem := memberInterLocus_preimage (Subtype.val : openPreimage T U → Y)
      (fun z => (openPreimage T U).isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq z)
      (geoTransformAlong (barMarked 𝔍) T).N (origMembers 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp
    unfold IsSpecial
    rw [hl, hO, hg]
    rw [← hc, hg] at hmem
    refine or_congr (and_congr_right fun _ => ?_) (and_congr_right fun _ => ?_)
    · rw [show codimOnePartAlong (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y)
          (geoTransformAlong (barMarked 𝔍) T)).N (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y)
          (geoTransformAlong (barMarked 𝔍) T)).ideal (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y)
          (geoTransformAlong (barMarked 𝔍) T)).d = _ from hcod]
      rfl
    · show p ∈ memberInterLocus ((Subtype.val : openPreimage T U → Y) ⁻¹' (geoTransformAlong (barMarked 𝔍) T).N)
          ((origMembers 𝔍 T).map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·))
          (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong (barMarked 𝔍) T)).cosupp ↔ _
      rw [hmem]
      rfl
  exact ⟨hl, hs, fun s => by unfold stepRegime; rw [hl, hs]⟩

/-- **The hypotheses of Step 1 pass to `𝔍|_U`.** -/
theorem hypotheses_restrict (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {k : ℕ}
    (hk : DimLE n 𝔍.N k) :
    (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).IsWellFormed ∧ 1 ≤ (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).d ∧
      IsMaximalOrderAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).N
        (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).ideal (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).d ∧
      DimLE n (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).N k := by
  refine ⟨IsWellFormed.pullback_val h𝔍 U, hd, fun x hx => ?_, fun p hp => ?_⟩
  · -- the cosupport of mark `d + 1` restricts
    let 𝔫 : MarkedIdeal n X := ⟨𝔍.N, 𝔍.E, 𝔍.ideal, 𝔍.d + 1⟩
    have h := cosupp_pullback_val 𝔫
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔍.isCoherent hg) U
    have hx' : x ∈ (MarkedIdeal.pullback (Subtype.val : U → X) 𝔫).cosupp := hx
    rw [h] at hx'
    exact hmax _ hx'
  · obtain ⟨j, hjk, hj⟩ := hk (p : X) hp
    exact ⟨j, hjk, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hj⟩

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **The values agree along `T` and `T|_U`** when both are canonical segments. -/
theorem stepOneInvM_restrict_eq (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T)
    (hcanU : IsCanonical (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (stepOneInvM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T))
    (p : openPreimage T U) (hp : (p : Y) ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) :
    stepOneInvM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p =
      stepOneInvM R 𝔍 T p := by
  obtain ⟨h𝔍U, hdU, hmaxU, hkU⟩ := hypotheses_restrict 𝔍 U h𝔍 hd hmax hk
  have hT := StepOneAdmissible.isGeoTestTower_of_isCanonical_stepOneInvM 𝔍 R h𝔍 hd hn hmax hk T hcan
  have hTU := StepOneAdmissible.isGeoTestTower_of_isCanonical_stepOneInvM (X := CMfd.of (n := n) U) _ R h𝔍U hdU hn
    hmaxU hkU _ hcanU
  obtain ⟨-, hc, hpt⟩ := restrict_facts 𝔍 U h𝔍 hd T hT
  obtain ⟨hl, hs, -⟩ := hpt p
  have hpU : p ∈ (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (restrict U T)).cosupp := by rw [hc]; exact hp
  have hD := hasLowerDataL_of_isCanonical 𝔍 R h𝔍 hd hn hmax hk T hT hcan p hp
  have hDU := hasLowerDataL_of_isCanonical (X := CMfd.of (n := n) U) _ R h𝔍U hdU hn hmaxU hkU _ hTU hcanU p hpU
  by_cases hsp : IsSpecial 𝔍 T p
  · show stepOneInvL (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
      (lowerMarkedM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T) p =
      stepOneInvL R 𝔍 (lowerMarkedM 𝔍) T (p : Y)
    rw [stepOneInvL_of_isSpecial (X := CMfd.of (n := n) U) R _ _ _ (hs.mpr hsp), stepOneInvL_of_isSpecial R 𝔍 _ T hsp, hl]
  · have hspU : ¬ IsSpecial (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p :=
      fun h => hsp (hs.mp h)
    specialize hD hsp
    specialize hDU hspU
    show stepOneInvL (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
      (lowerMarkedM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T) p =
      stepOneInvL R 𝔍 (lowerMarkedM 𝔍) T (p : Y)
    rw [stepOneInvL_of_not_isSpecial (X := CMfd.of (n := n) U) R _ _ _ hspU, stepOneInvL_of_not_isSpecial R 𝔍 _ T hsp]
    rw [hl] at hDU ⊢
    obtain ⟨s, hsdef⟩ : ∃ s, level 𝔍 T p = s := ⟨_, rfl⟩
    rw [hsdef] at hD hDU ⊢
    have hrun := NonmonomialOrderRegime.regimeRun_restrict_of U (stepRegime 𝔍 s)
      (stepRegime (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) s)
      (fun T' => IsGeoTestTower (barMarked 𝔍) T') (fun _ _ _ _ h => h.1)
      (fun T' hT' q => ((restrict_facts 𝔍 U h𝔍 hd T' hT').2.2 q).2.2 s) T hT p
    rw [hrun] at hDU ⊢
    obtain ⟨χ₀, h₀, h₁⟩ := BlowupTowerSplitIso.exists_isTowerIso_split_restrict U T (regimeRun (stepRegime 𝔍 s) T p)
    have hT₀₁ : IsGeoTestTower (barMarked 𝔍) ((head T (regimeRun (stepRegime 𝔍 s) T p)).append
        (tail T (regimeRun (stepRegime 𝔍 s) T p))) := by rw [head_append_tail]; exact hT
    congr 2
    rcases s with _ | s
    · exact ContactLowerValue.lowerValueL_zero_restrict U R 𝔍 h𝔍 hd h₀ h₁ hT₀₁
        (by rw [head_append_tail]; exact hp) hDU hD
    · exact MemberRestrictTowerIso.lowerValueL_succ_restrict U R 𝔍 h𝔍 hd hn h₀ h₁ hT₀₁ hDU hD

/-- **Property (5) of the masked Step 1 value function** (`hir:step-one-restrict-open`; the field `restrictOpen` of
`ResolutionInvariantExt.ResolutionInvariant`, with the restriction of canonical segments): for `𝔍` well formed with `d ≥ 1`, of
maximal order along `N` with `dim N ≤ k` (`0 < n`), `R` a resolution invariant in dimension `≤ k - 1` and `U ⊆ X` open, the
restriction `T|_U` of a canonical segment `T` of `stepOneInvM R 𝔍` is a canonical segment of `stepOneInvM R 𝔍|_U`, and at the
points of the cosupport over `U` the values agree (induction on `T`: the trace of the maximum locus is empty or the maximum locus
of the restriction, `ResolutionInvariantSegments.maxLocus_preimage`). -/
theorem stepOneInvM_restrict (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T →
      IsCanonical (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
        (stepOneInvM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T) ∧
      ∀ p : openPreimage T U, (p : Y) ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp →
        stepOneInvM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p =
          stepOneInvM R 𝔍 T p
  | _, .refl, hcan => ⟨trivial, fun p hp => stepOneInvM_restrict_eq 𝔍 U R h𝔍 hd hn hmax hk .refl hcan trivial p hp⟩
  | _, .step T C π hπ, hcan => by
      have hcan₀ := hcan
      obtain ⟨hcanT, hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T ∧
          (C = ∅ ∨ C = maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp) := hcan
      obtain ⟨hcanUT, hval⟩ := stepOneInvM_restrict h𝔍 hd hn hmax hk T hcanT
      have hT := StepOneAdmissible.isGeoTestTower_of_isCanonical_stepOneInvM 𝔍 R h𝔍 hd hn hmax hk T hcanT
      have hc := (restrict_facts 𝔍 U h𝔍 hd T hT).2.1
      have hcanUS : IsCanonical (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
          (stepOneInvM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
          (restrict U (.step T C π hπ)) := by
        show IsCanonical (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
            (stepOneInvM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T) ∧
          (((Subtype.val : openPreimage T U → _) ⁻¹' C) = ∅ ∨
            ((Subtype.val : openPreimage T U → _) ⁻¹' C) = maxLocus
              (stepOneInvM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T))
              (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
                (restrict U T)).cosupp)
        refine ⟨hcanUT, ?_⟩
        rcases hC with rfl | rfl
        · exact Or.inl preimage_empty
        · by_cases hne : ((Subtype.val : openPreimage T U → _) ⁻¹'
              maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp).Nonempty
          · right
            rw [hc]
            exact (ResolutionInvariantSegments.maxLocus_preimage _ (fun q hq => hval q hq) hne).symm
          · exact Or.inl (not_nonempty_iff_eq_empty.mp hne)
      exact ⟨hcanUS, fun p hp => stepOneInvM_restrict_eq 𝔍 U R h𝔍 hd hn hmax hk _ hcan₀ hcanUS p hp⟩

end Restrict

end

end Hironaka.StepOneRestrictOpen
