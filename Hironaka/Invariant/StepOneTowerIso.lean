/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneRestrictOpen
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerSplitIso
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
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Invariant.MemberRestrictTowerIso
import Hironaka.Invariant.NonmonomialOrderRegime
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
# Step 1: isomorphisms of towers (property (6))

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`: the resolution commutes with étale
morphisms, in particular with biholomorphisms.

For a biholomorphism `Φ: X' ≅ X` and an isomorphism of towers `χ: T' ≅ T` over `Φ`
(`BlowupTowerIsomorphism.IsTowerIso`), the masked Step 1 values of `Φ^*𝔍` along `T'` are those of `𝔍` along `T`
(through `χ`), and canonical segments correspond. `J̄(Φ^*𝔍) = Φ^*J̄(𝔍)` (`ContactStageKept.barMarked_pullback`) and
transforms correspond along isomorphisms of towers (`IsTowerIso.geoTransformAlong_eq`), so the original members
(`ContactLowerValue.origMembers_isTowerIso`), levels, special points (codimension-one part and member locus under
biholomorphisms) and regimes are preimages; runs agree (`NonmonomialOrderRegime.regimeRun_isTowerIso_of`); splits
correspond (`BlowupTowerSplitIso.IsTowerIso.exists_split`); the lower values agree by
`ContactLowerValue.lowerValueL_zero_isTowerIso` (level `0`) and `MemberRestrictTowerIso.lowerValueL_succ_isTowerIso`
(levels `≥ 1`).

## Main results

* `geoTransformAlong_barMarked_isTowerIso`, `isTowerIso_facts`, `hypotheses_pullback`;
* `stepOneInvM_isTowerIso_eq`, **`stepOneInvM_isTowerIso`**: property (6).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneTowerIso

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime Hironaka.StepOneValue Hironaka.StepOneLowerDomain Hironaka.StepOneValueMasked Hironaka.StepOneCanonicalTail Hironaka.HomogenizedIdealAlong Hironaka.CodimOneSupportAlong Hironaka.MemberInterLocusAlong Hironaka.MarkedIdealBiholomorphism Hironaka.BlowupTowerIsomorphism Hironaka.MarkedIdealRestrictOpen
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)

noncomputable section

variable {n : ℕ}

section TowerIso

variable {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (𝔍 : MarkedIdeal n X)

/-- **The marked ideal of Step 1 of `Φ^*𝔍` along `T'`** is the transport of that of `𝔍` along `T` (`χ : T' ≅ T` over `Φ`, `T` a
multiple test blow-up of `J̄`). -/
theorem geoTransformAlong_barMarked_isTowerIso (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y' Y : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y} {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower (barMarked 𝔍) T) :
    geoTransformAlong (barMarked (MarkedIdeal.pullback Φ 𝔍)) T' =
      MarkedIdeal.pullback χ (geoTransformAlong (barMarked 𝔍) T) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  rw [show barMarked (MarkedIdeal.pullback Φ 𝔍) = MarkedIdeal.pullback Φ (barMarked 𝔍) from
    ContactStageKept.barMarked_pullback Φ h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd]
  exact IsTowerIso.geoTransformAlong_eq Φ hJ.isClosedSubmanifold_N hJ.isCoherent hiso hT

/-- **Levels, special points, regimes and the cosupport along `T'`** are the preimages of those along `T`. -/
theorem isTowerIso_facts (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y' Y : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y} {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower (barMarked 𝔍) T) :
    IsGeoTestTower (barMarked (MarkedIdeal.pullback Φ 𝔍)) T' ∧
      (geoTransformAlong (barMarked (MarkedIdeal.pullback Φ 𝔍)) T').cosupp = χ ⁻¹' (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
      ∀ p : Y', level (MarkedIdeal.pullback Φ 𝔍) T' p = level 𝔍 T (χ p) ∧
        (IsSpecial (MarkedIdeal.pullback Φ 𝔍) T' p ↔ IsSpecial 𝔍 T (χ p)) ∧
        ∀ s, stepRegime (MarkedIdeal.pullback Φ 𝔍) s T' p ↔ stepRegime 𝔍 s T (χ p) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T hT
  have hg := geoTransformAlong_barMarked_isTowerIso Φ 𝔍 h𝔍 hd hiso hT
  have htest : IsGeoTestTower (barMarked (MarkedIdeal.pullback Φ 𝔍)) T' := by
    rw [show barMarked (MarkedIdeal.pullback Φ 𝔍) = MarkedIdeal.pullback Φ (barMarked 𝔍) from
      ContactStageKept.barMarked_pullback Φ h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd]
    exact (IsTowerIso.isGeoTestTower_iff Φ hJ.isClosedSubmanifold_N hJ.isCoherent hiso).mpr hT
  have hc : (geoTransformAlong (barMarked (MarkedIdeal.pullback Φ 𝔍)) T').cosupp =
      χ ⁻¹' (geoTransformAlong (barMarked 𝔍) T).cosupp := by
    rw [hg]
    exact MarkedIdealTowerTransport.cosupp_pullback_eq hcT
  have hO := ContactLowerValue.origMembers_isTowerIso Φ 𝔍 h𝔍 hd hiso hT
  refine ⟨htest, hc, fun p => ?_⟩
  have hl : level (MarkedIdeal.pullback Φ 𝔍) T' p = level 𝔍 T (χ p) := by
    unfold level
    rw [hO]
    exact CodimOnePartCanonical.boundaryCount_map_preimage χ _ p
  have hs : IsSpecial (MarkedIdeal.pullback Φ 𝔍) T' p ↔ IsSpecial 𝔍 T (χ p) := by
    have hcod := CodimOnePartCanonical.codimOnePartAlong_pullback χ (𝔞 := (geoTransformAlong (barMarked 𝔍) T).ideal)
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg)
      (N := (geoTransformAlong (barMarked 𝔍) T).N) (geoTransformAlong (barMarked 𝔍) T).d
    have hmem := memberInterLocus_preimage (χ : Y' → Y) (fun z => χ.toHomeomorph.map_nhds_eq z)
      (geoTransformAlong (barMarked 𝔍) T).N (origMembers 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp
    unfold IsSpecial
    rw [hl, hO, hg]
    rw [← hc, hg] at hmem
    refine or_congr (and_congr_right fun _ => ?_) (and_congr_right fun _ => ?_)
    · rw [show codimOnePartAlong (MarkedIdeal.pullback χ (geoTransformAlong (barMarked 𝔍) T)).N
          (MarkedIdeal.pullback χ (geoTransformAlong (barMarked 𝔍) T)).ideal
          (MarkedIdeal.pullback χ (geoTransformAlong (barMarked 𝔍) T)).d = _ from hcod]
      rfl
    · show p ∈ memberInterLocus ((χ : Y' → Y) ⁻¹' (geoTransformAlong (barMarked 𝔍) T).N)
          ((origMembers 𝔍 T).map ((χ : Y' → Y) ⁻¹' ·))
          (MarkedIdeal.pullback χ (geoTransformAlong (barMarked 𝔍) T)).cosupp ↔ _
      rw [hmem]
      rfl
  exact ⟨hl, hs, fun s => by unfold stepRegime; rw [hl, hs]⟩

/-- **The hypotheses of Step 1 pass to `Φ^*𝔍`.** -/
theorem hypotheses_pullback (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {k : ℕ}
    (hk : DimLE n 𝔍.N k) :
    (MarkedIdeal.pullback Φ 𝔍).IsWellFormed ∧ 1 ≤ (MarkedIdeal.pullback Φ 𝔍).d ∧
      IsMaximalOrderAlong (MarkedIdeal.pullback Φ 𝔍).N (MarkedIdeal.pullback Φ 𝔍).ideal (MarkedIdeal.pullback Φ 𝔍).d ∧
      DimLE n (MarkedIdeal.pullback Φ 𝔍).N k := by
  refine ⟨MarkedIdealTowerTransport.IsWellFormed.pullback (Φ := Φ) h𝔍, hd, fun x hx => ?_, fun p hp => ?_⟩
  · have h := CodimOnePartCanonical.cosupport_pullback Φ (N := 𝔍.N)
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔍.isCoherent hg) (𝔍.d + 1)
    have hx' : x ∈ GermIdealOrder.cosupport n (Φ ⁻¹' 𝔍.N) (GermIdeal.pullback (m := n) Φ 𝔍.ideal) (𝔍.d + 1) := hx
    rw [h] at hx'
    exact hmax _ hx'
  · obtain ⟨j, hjk, hj⟩ := hk (Φ p) hp
    exact ⟨j, hjk, (CodimOnePartCanonical.regularAtDim_preimage_iff Φ).mpr hj⟩

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **The values agree along isomorphic towers** when both are canonical segments. -/
theorem stepOneInvM_isTowerIso_eq (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y' Y : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y} {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T)
    (hcan' : IsCanonical (barMarked (MarkedIdeal.pullback Φ 𝔍)) (stepOneInvM R (MarkedIdeal.pullback Φ 𝔍)) T')
    (p : Y') (hp : χ p ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) :
    stepOneInvM R (MarkedIdeal.pullback Φ 𝔍) T' p = stepOneInvM R 𝔍 T (χ p) := by
  obtain ⟨h𝔍', hd', hmax', hk'⟩ := hypotheses_pullback Φ 𝔍 h𝔍 hd hmax hk
  have hT := StepOneAdmissible.isGeoTestTower_of_isCanonical_stepOneInvM 𝔍 R h𝔍 hd hn hmax hk T hcan
  have hT' := StepOneAdmissible.isGeoTestTower_of_isCanonical_stepOneInvM _ R h𝔍' hd' hn hmax' hk' T' hcan'
  obtain ⟨-, hc, hpt⟩ := isTowerIso_facts Φ 𝔍 h𝔍 hd hiso hT
  obtain ⟨hl, hs, -⟩ := hpt p
  have hp' : p ∈ (geoTransformAlong (barMarked (MarkedIdeal.pullback Φ 𝔍)) T').cosupp := by rw [hc]; exact hp
  have hD := hasLowerDataL_of_isCanonical 𝔍 R h𝔍 hd hn hmax hk T hT hcan (χ p) hp
  have hD' := hasLowerDataL_of_isCanonical _ R h𝔍' hd' hn hmax' hk' T' hT' hcan' p hp'
  by_cases hsp : IsSpecial 𝔍 T (χ p)
  · show stepOneInvL R (MarkedIdeal.pullback Φ 𝔍) (lowerMarkedM (MarkedIdeal.pullback Φ 𝔍)) T' p =
      stepOneInvL R 𝔍 (lowerMarkedM 𝔍) T (χ p)
    rw [stepOneInvL_of_isSpecial R _ _ T' (hs.mpr hsp), stepOneInvL_of_isSpecial R 𝔍 _ T hsp, hl]
  · have hsp' : ¬ IsSpecial (MarkedIdeal.pullback Φ 𝔍) T' p := fun h => hsp (hs.mp h)
    specialize hD hsp
    specialize hD' hsp'
    show stepOneInvL R (MarkedIdeal.pullback Φ 𝔍) (lowerMarkedM (MarkedIdeal.pullback Φ 𝔍)) T' p =
      stepOneInvL R 𝔍 (lowerMarkedM 𝔍) T (χ p)
    rw [stepOneInvL_of_not_isSpecial R _ _ T' hsp', stepOneInvL_of_not_isSpecial R 𝔍 _ T hsp]
    rw [hl] at hD' ⊢
    obtain ⟨s, hsdef⟩ : ∃ s, level 𝔍 T (χ p) = s := ⟨_, rfl⟩
    rw [hsdef] at hD hD' ⊢
    have hrun := NonmonomialOrderRegime.regimeRun_isTowerIso_of (stepRegime 𝔍 s)
      (stepRegime (MarkedIdeal.pullback Φ 𝔍) s) (fun S => IsGeoTestTower (barMarked 𝔍) S) (fun _ _ _ _ h => h.1)
      (fun S' S ψ hψ hS q => ((isTowerIso_facts Φ 𝔍 h𝔍 hd hψ hS).2.2 q).2.2 s) hiso hT p
    rw [hrun] at hD' ⊢
    obtain ⟨χ₀, h₀, h₁⟩ := BlowupTowerSplitIso.IsTowerIso.exists_split hiso (regimeRun (stepRegime 𝔍 s) T (χ p))
    have hT₀₁ : IsGeoTestTower (barMarked 𝔍) ((head T (regimeRun (stepRegime 𝔍 s) T (χ p))).append
        (tail T (regimeRun (stepRegime 𝔍 s) T (χ p)))) := by rw [head_append_tail]; exact hT
    congr 2
    rcases s with _ | s
    · exact ContactLowerValue.lowerValueL_zero_isTowerIso Φ R 𝔍 h𝔍 hd h₀ h₁ hT₀₁
        (by rw [head_append_tail]; exact hp) hD' hD
    · exact MemberRestrictTowerIso.lowerValueL_succ_isTowerIso Φ R 𝔍 h𝔍 hd hn h₀ h₁ hT₀₁ hD' hD

/-- **Property (6) of the masked Step 1 value function** (`hir:step-one-tower-iso`; the field `towerIso` of
`ResolutionInvariantExt.ResolutionInvariant`, with the correspondence of canonical segments): for `𝔍` well formed with `d ≥ 1`, of
maximal order along `N` with `dim N ≤ k` (`0 < n`), `R` a resolution invariant in dimension `≤ k - 1`, `Φ : X' ≅ X` and an
isomorphism `χ : T' ≅ T` of towers over `Φ` with `T` a canonical segment of `stepOneInvM R 𝔍`, the tower `T'` is a canonical
segment of `stepOneInvM R Φ^*𝔍` and `stepOneInvM R Φ^*𝔍 T' p = stepOneInvM R 𝔍 T (χ p)` at the points with `χ p` in the cosupport
(induction on the isomorphism; the maximum loci correspond, `ResolutionInvariantSegments.maxLocus_preimage_of_surjective`). -/
theorem stepOneInvM_isTowerIso (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y' Y : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y} {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) :
    IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T →
      IsCanonical (barMarked (MarkedIdeal.pullback Φ 𝔍)) (stepOneInvM R (MarkedIdeal.pullback Φ 𝔍)) T' ∧
      ∀ p : Y', χ p ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp →
        stepOneInvM R (MarkedIdeal.pullback Φ 𝔍) T' p = stepOneInvM R 𝔍 T (χ p) := by
  induction hiso with
  | refl =>
    intro hcan
    exact ⟨trivial, fun p hp => stepOneInvM_isTowerIso_eq Φ 𝔍 R h𝔍 hd hn hmax hk IsTowerIso.refl hcan trivial p hp⟩
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro hcan
    have hcan₀ := hcan
    obtain ⟨hcanT, hCc⟩ : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T ∧
        (C = ∅ ∨ C = maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp) := hcan
    obtain ⟨hcan'T, hval⟩ := ih hcanT
    have hT := StepOneAdmissible.isGeoTestTower_of_isCanonical_stepOneInvM 𝔍 R h𝔍 hd hn hmax hk T hcanT
    have hc := (isTowerIso_facts Φ 𝔍 h𝔍 hd h hT).2.1
    have hcan'S : IsCanonical (barMarked (MarkedIdeal.pullback Φ 𝔍)) (stepOneInvM R (MarkedIdeal.pullback Φ 𝔍))
        (.step T' C' π' hπ') := by
      show IsCanonical (barMarked (MarkedIdeal.pullback Φ 𝔍)) (stepOneInvM R (MarkedIdeal.pullback Φ 𝔍)) T' ∧
        (C' = ∅ ∨ C' = maxLocus (stepOneInvM R (MarkedIdeal.pullback Φ 𝔍) T')
          (geoTransformAlong (barMarked (MarkedIdeal.pullback Φ 𝔍)) T').cosupp)
      refine ⟨hcan'T, ?_⟩
      subst hC
      rcases hCc with rfl | rfl
      · exact Or.inl preimage_empty
      · right
        rw [hc]
        exact (ResolutionInvariantSegments.maxLocus_preimage_of_surjective χ.toEquiv.surjective
          (fun q hq => hval q hq)).symm
    exact ⟨hcan'S, fun p hp => stepOneInvM_isTowerIso_eq Φ 𝔍 R h𝔍 hd hn hmax hk
      (IsTowerIso.step h hπ' hπ χ₁ hcomm hC) hcan₀ hcan'S p hp⟩

end TowerIso

end

end Hironaka.StepOneTowerIso
