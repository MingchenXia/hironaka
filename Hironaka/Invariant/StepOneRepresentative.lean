/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneEmptyPrefix
import Hironaka.Invariant.MemberRestrictTowerIso
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.BoundaryCount
import Hironaka.MarkedIdeal.CodimOneSupportAlong
import Hironaka.Invariant.ContactLowerValue
import Hironaka.Invariant.ContactRepresentative
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantExt
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
# Step 1: independence of the representative (property (7))

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`: the invariant depends only on the
equivalence class of the marked ideal (the resolution of equivalent marked ideals is the same).

For restricted-equivalent marked ideals `𝔍 ≃ 𝔍'` (`MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv`: same `N`,
`E`, `d`, the ideals agree on `N`), the masked Step 1 values agree along canonical segments, which are the same for
both: `J̄ ≃ J̄'` (`ContactRepresentative.restrictEquiv_barMarked`), so the transforms along every tower have the
same `N` and cosupport; the original members are the same (`ContactLowerValue.origMembers_restrictEquiv`), so are
levels, special points, regimes and runs; the lower values agree by
`ContactLowerValue.lowerValueL_zero_representative` (level `0`) and
`MemberRestrictTowerIso.lowerValueL_succ_representative` (levels `≥ 1`).

## Main results

* `regimeRun_congr`: runs of pointwise equivalent regimes agree;
* `isSpecial_iff_of_eq`: special points from the original members, `N` and the cosupport;
* `stepOneInvM_representative_eq`, **`stepOneInvM_representative`**: property (7).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneRepresentative

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime Hironaka.StepOneValue Hironaka.StepOneLowerDomain Hironaka.StepOneValueMasked Hironaka.StepOneCanonicalTail Hironaka.HomogenizedIdealAlong Hironaka.CodimOneSupportAlong Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)

noncomputable section

variable {n : ℕ}

/-! ### Generic tools -/

section Tools

/-- **Runs of pointwise equivalent regimes agree.** -/
theorem regimeRun_congr {X : CMfd.{u} n} (Q Q' : Regime X)
    (hQ : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y), Q T y ↔ Q' T y) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (z : Y), regimeRun Q T z = regimeRun Q' T z
  | _, .refl, _ => rfl
  | _, .step T C π hπ, z => by
      by_cases hq : Q T (π z)
      · rw [regimeRun_step_of Q T C π hπ hq, regimeRun_step_of Q' T C π hπ ((hQ T (π z)).mp hq),
          regimeRun_congr Q Q' hQ T (π z)]
      · rw [regimeRun_step_of_not Q T C π hπ hq,
          regimeRun_step_of_not Q' T C π hπ (fun h => hq ((hQ T (π z)).mpr h))]

/-- **Special points from the original members, `N` and the cosupport**: two marked ideals and towers ending at the same stage
with the same original members, and the same `N` and cosupport of the transforms of the marked ideals of Step 1, have the
same special points. -/
theorem isSpecial_iff_of_eq {X X' Y : CMfd.{u} n} (𝔍 : MarkedIdeal n X) (𝔍' : MarkedIdeal n X') (T : BlowupTower X Y)
    (T' : BlowupTower X' Y) (hO : origMembers 𝔍 T = origMembers 𝔍' T')
    (hN : (geoTransformAlong (barMarked 𝔍) T).N = (geoTransformAlong (barMarked 𝔍') T').N)
    (hC : (geoTransformAlong (barMarked 𝔍) T).cosupp = (geoTransformAlong (barMarked 𝔍') T').cosupp) (y : Y) :
    IsSpecial 𝔍 T y ↔ IsSpecial 𝔍' T' y := by
  have hco : GermIdealOrder.cosupport n (geoTransformAlong (barMarked 𝔍) T).N (geoTransformAlong (barMarked 𝔍) T).ideal
      (geoTransformAlong (barMarked 𝔍) T).d = GermIdealOrder.cosupport n (geoTransformAlong (barMarked 𝔍') T').N
        (geoTransformAlong (barMarked 𝔍') T').ideal (geoTransformAlong (barMarked 𝔍') T').d := hC
  unfold IsSpecial level codimOnePartAlong
  rw [hO, hco, hC, hN]

end Tools

/-! ### Property (7) -/

section Representative

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n (k - 1) Λ)
  {𝔍 𝔍' : MarkedIdeal n X}

/-- **Levels, special points and regimes of restricted-equivalent marked ideals agree** along every tower, and so do the `N`
and the cosupports of the transforms of their marked ideals of Step 1. -/
theorem restrictEquiv_facts (h𝔍 : 𝔍.IsWellFormed) (h𝔞' : 𝔍'.ideal.IsCoherent) (hEq : RestrictEquiv 𝔍 𝔍') :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong (barMarked 𝔍) T).N = (geoTransformAlong (barMarked 𝔍') T).N ∧
      (geoTransformAlong (barMarked 𝔍) T).cosupp = (geoTransformAlong (barMarked 𝔍') T).cosupp ∧
      (IsGeoTestTower (barMarked 𝔍) T ↔ IsGeoTestTower (barMarked 𝔍') T) ∧
      ∀ y : Y, level 𝔍 T y = level 𝔍' T y ∧ (IsSpecial 𝔍 T y ↔ IsSpecial 𝔍' T y) ∧
        ∀ s, stepRegime 𝔍 s T y ↔ stepRegime 𝔍' s T y := by
  intro Y T
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hJJ : RestrictEquiv (barMarked 𝔍) (barMarked 𝔍') :=
    ContactRepresentative.restrictEquiv_barMarked hEq h𝔍.isClosedSubmanifold_N h𝔍.isCoherent h𝔞'
  have hJ'c : (barMarked 𝔍').ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞' (hEq.N_eq ▸ h𝔍.isClosedSubmanifold_N))
      (hEq.N_eq ▸ h𝔍.isClosedSubmanifold_N)
  have hC := (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong hJJ
    hJ.isClosedSubmanifold_N.1 hJ.isCoherent hJ'c T).1
  have hN : (geoTransformAlong (barMarked 𝔍) T).N = (geoTransformAlong (barMarked 𝔍') T).N := by
    cases T with
    | refl => exact hJJ.N_eq
    | step T C π hπ =>
      rw [MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq hJJ hJ.isClosedSubmanifold_N.1
        hJ.isCoherent hJ'c T C π hπ]
  have hO : origMembers 𝔍 T = origMembers 𝔍' T := (ContactLowerValue.origMembers_restrictEquiv hEq T).symm
  have htest := ((MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hJJ hJ.isClosedSubmanifold_N.1 hJ.isCoherent
    hJ'c).2 T).1
  refine ⟨hN, hC, htest, fun y => ?_⟩
  have hl : level 𝔍 T y = level 𝔍' T y := by unfold level; rw [hO]
  have hs := isSpecial_iff_of_eq 𝔍 𝔍' T T hO hN hC y
  exact ⟨hl, hs, fun s => by unfold stepRegime; rw [hl, hs]⟩

/-- **The values agree along common canonical segments** (`𝔍 ≃ 𝔍'`, both satisfying the hypotheses of Step 1). -/
theorem stepOneInvM_representative_eq (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) (h𝔍' : 𝔍'.IsWellFormed) (hd' : 1 ≤ 𝔍'.d)
    (hmax' : IsMaximalOrderAlong 𝔍'.N 𝔍'.ideal 𝔍'.d) (hk' : DimLE n 𝔍'.N k) (hEq : RestrictEquiv 𝔍 𝔍')
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T)
    (hcan' : IsCanonical (barMarked 𝔍') (stepOneInvM R 𝔍') T) {y : Y}
    (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) :
    stepOneInvM R 𝔍 T y = stepOneInvM R 𝔍' T y := by
  have hT := StepOneAdmissible.isGeoTestTower_of_isCanonical_stepOneInvM 𝔍 R h𝔍 hd hn hmax hk T hcan
  have hT' := StepOneAdmissible.isGeoTestTower_of_isCanonical_stepOneInvM 𝔍' R h𝔍' hd' hn hmax' hk' T hcan'
  obtain ⟨-, hC, -, hpt⟩ := restrictEquiv_facts h𝔍 h𝔍'.isCoherent hEq T
  obtain ⟨hl, hs, -⟩ := hpt y
  have hy' : y ∈ (geoTransformAlong (barMarked 𝔍') T).cosupp := hC ▸ hy
  have hD := hasLowerDataL_of_isCanonical 𝔍 R h𝔍 hd hn hmax hk T hT hcan y hy
  have hD' := hasLowerDataL_of_isCanonical 𝔍' R h𝔍' hd' hn hmax' hk' T hT' hcan' y hy'
  by_cases hsp : IsSpecial 𝔍 T y
  · show stepOneInvL R 𝔍 _ _ y = stepOneInvL R 𝔍' _ _ y
    rw [stepOneInvL_of_isSpecial R 𝔍 _ T hsp, stepOneInvL_of_isSpecial R 𝔍' _ T (hs.mp hsp), hl]
  · have hsp' : ¬ IsSpecial 𝔍' T y := fun h => hsp (hs.mpr h)
    specialize hD hsp
    specialize hD' hsp'
    show stepOneInvL R 𝔍 _ _ y = stepOneInvL R 𝔍' _ _ y
    rw [stepOneInvL_of_not_isSpecial R 𝔍 _ T hsp, stepOneInvL_of_not_isSpecial R 𝔍' _ T hsp']
    rw [← hl] at hD' ⊢
    obtain ⟨s, hsdef⟩ : ∃ s, level 𝔍 T y = s := ⟨_, rfl⟩
    rw [hsdef] at hD hD' ⊢
    have hrun := regimeRun_congr (stepRegime 𝔍 s) (stepRegime 𝔍' s) (fun T' y' => ((restrictEquiv_facts h𝔍 h𝔍'.isCoherent hEq T').2.2.2 y').2.2 s) T y
    rw [hrun] at hD ⊢
    have hT₀₁ : IsGeoTestTower (barMarked 𝔍) ((head T (regimeRun (stepRegime 𝔍' s) T y)).append
        (tail T (regimeRun (stepRegime 𝔍' s) T y))) := by rw [head_append_tail]; exact hT
    congr 2
    rcases s with _ | s
    · have hp : y ∈ (geoTransformAlong (barMarked 𝔍) ((head T (regimeRun (stepRegime 𝔍' 0) T y)).append
          (tail T (regimeRun (stepRegime 𝔍' 0) T y)))).cosupp := by rw [head_append_tail]; exact hy
      exact ContactLowerValue.lowerValueL_zero_representative R h𝔍 h𝔍'.isCoherent hd hEq _ _ hT₀₁ hp hD hD'
    · exact MemberRestrictTowerIso.lowerValueL_succ_representative R h𝔍 h𝔍'.isCoherent hn hEq _ _ hT₀₁ hD hD'

/-- **Property (7) of the masked Step 1 value function** (`hir:step-one-representative`; the field `representative` of
`ResolutionInvariantExt.ResolutionInvariant`, with the canonicity of the segment for `𝔍'` added): for restricted-equivalent
`𝔍 ≃ 𝔍'`, both well formed with `d ≥ 1`, of maximal order along `N` with `dim N ≤ k` (`0 < n`), and `R` a resolution invariant in
dimension `≤ k - 1`, every canonical segment `T` of `stepOneInvM R 𝔍` is one of `stepOneInvM R 𝔍'`, and the two values agree on the
cosupport of `J̄_T` (induction on `T`: the maximum loci agree once the values and the cosupports do). -/
theorem stepOneInvM_representative (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) (h𝔍' : 𝔍'.IsWellFormed) (hd' : 1 ≤ 𝔍'.d)
    (hmax' : IsMaximalOrderAlong 𝔍'.N 𝔍'.ideal 𝔍'.d) (hk' : DimLE n 𝔍'.N k) (hEq : RestrictEquiv 𝔍 𝔍') :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T →
      IsCanonical (barMarked 𝔍') (stepOneInvM R 𝔍') T ∧
        ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, stepOneInvM R 𝔍 T y = stepOneInvM R 𝔍' T y
  | _, .refl, hcan => ⟨trivial, fun _ hy =>
      stepOneInvM_representative_eq R h𝔍 hd hn hmax hk h𝔍' hd' hmax' hk' hEq .refl hcan trivial hy⟩
  | _, .step T C π hπ, hcan => by
      have hcan₀ := hcan
      obtain ⟨hcanT, hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T ∧
          (C = ∅ ∨ C = maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp) := hcan
      obtain ⟨hcan'T, hval⟩ := stepOneInvM_representative h𝔍 hd hn hmax hk h𝔍' hd' hmax' hk' hEq T hcanT
      have hcosT := (restrictEquiv_facts h𝔍 h𝔍'.isCoherent hEq T).2.1
      have hcan'S : IsCanonical (barMarked 𝔍') (stepOneInvM R 𝔍') (.step T C π hπ) := by
        refine (⟨hcan'T, hC.imp id fun h => h.trans ?_⟩ :
          IsCanonical (barMarked 𝔍') (stepOneInvM R 𝔍') T ∧
            (C = ∅ ∨ C = maxLocus (stepOneInvM R 𝔍' T) (geoTransformAlong (barMarked 𝔍') T).cosupp))
        rw [← hcosT]
        exact ResolutionInvariantExt.maxLocus_congr hval
      exact ⟨hcan'S, fun _ hy =>
        stepOneInvM_representative_eq R h𝔍 hd hn hmax hk h𝔍' hd' hmax' hk' hEq _ hcan₀ hcan'S hy⟩

end Representative

end

end Hironaka.StepOneRepresentative
