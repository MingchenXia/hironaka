/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneCanonicalTail
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.BoundaryCount
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantOrder
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.Invariant.StepOneRegime
import Hironaka.Invariant.StepOneValue
import Hironaka.Invariant.StepOneValueMasked
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1: upper semicontinuity of the value

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 1: the invariant of Step 1 is
`(s(x), inv_{k-1}(x))` with `s` the number of original divisor members through `x` (upper semicontinuous, the
members being closed) and `inv_{k-1}` the lower-dimensional invariant of the restricted marked ideal on a
neighbourhood of `x` (upper semicontinuous by induction).

Property (2) of the Step 1 value function (`hir:centre-function`, "upper semicontinuity on the cosupport") for the masked
value `StepOneValueMasked.stepOneInvM`, along canonical segments which are multiple test blow-ups of `J̄`:

* at a special point `x` of level `s` the value is `(s, ∞)`, the largest value of level `s`, and the level is upper
  semicontinuous (`BoundaryCount.eventually_boundaryCount_le`);
* at a non-special point `x` of level `s`, `x` has lower data (`StepOneCanonicalTail.hasLowerDataL_of_isCanonical`): over the
  open preimage of its mask the points of the cosupport have level `≤ s`, those of level `s` lie in the cosupport of the lower marked ideal along the restricted tail, where the value is `(s, R(q))` (`StepOneCanonicalTail.stepOneInvM_eq_lower`), and
  `R` is upper semicontinuous there (the field `usc` of `R`).

## Main results

* `eventually_level_le`: the level is upper semicontinuous;
* `eventually_forall_mem_of_eventually`: an eventual property on an open subtype, pushed to the ambient space;
* `stepOneInvM_eventually_le_of_not_isSpecial`, **`stepOneInvM_usc`**: property (2).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneUSC

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime Hironaka.StepOneValue Hironaka.StepOneLowerDomain Hironaka.StepOneMaskTower Hironaka.StepOneValueMasked Hironaka.StepOneCanonicalTail Hironaka.BoundaryCount Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen Hironaka.HomogenizedIdealAlong Hironaka.ResolutionInvariantOrder
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Tools -/

section Tools

/-- **An eventual property on an open subtype, pushed to the ambient space**: if `Q` holds eventually near `⟨x, hx⟩` in the
open `P`, then near `x` every point of `P` satisfies `Q`. -/
theorem eventually_forall_mem_of_eventually {M : Type*} [TopologicalSpace M] (P : Opens M) {x : M} (hx : x ∈ P)
    {Q : P → Prop} (h : ∀ᶠ q in 𝓝 (⟨x, hx⟩ : P), Q q) : ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ P, Q ⟨y, hy⟩ := by
  have hmap := P.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq (⟨x, hx⟩ : P)
  have h' : ∀ᶠ y in Filter.map (Subtype.val : P → M) (𝓝 (⟨x, hx⟩ : P)), ∀ hy : y ∈ P, Q ⟨y, hy⟩ :=
    Filter.eventually_map.mpr (h.mono fun q hq _ => hq)
  exact Filter.Eventually.filter_mono hmap.ge h'

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **The level is upper semicontinuous** (the original members are closed). -/
theorem eventually_level_le (hE : ∀ H ∈ 𝔍.E, IsClosed H) {Y : CMfd.{u} n} (T : BlowupTower X Y) (x : Y) :
    ∀ᶠ y in 𝓝 x, level 𝔍 T y ≤ level 𝔍 T x :=
  eventually_boundaryCount_le (isClosed_of_mem_origMembers 𝔍 hE T) x

end Tools

/-! ### Upper semicontinuity -/

section USC

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **Upper semicontinuity at a non-special point**: along a multiple test blow-up `T` of `J̄` which is a canonical segment of
`stepOneInvM R 𝔍`, near a non-special point `x` of the cosupport every point of the cosupport has value at most that of
`x` -- over the mask of `x` the points of level `s(x)` lie in the cosupport of the lower marked ideal, where the value is
`(s(x), R(·))`, and `R` is upper semicontinuous. -/
theorem stepOneInvM_eventually_le_of_not_isSpecial (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T) {x : Y}
    (hx : x ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) (hsp : ¬ IsSpecial 𝔍 T x) :
    ∀ᶠ y in 𝓝 x, y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp → stepOneInvM R 𝔍 T y ≤ stepOneInvM R 𝔍 T x := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  set s := level 𝔍 T x with hs
  set r := regimeRun (stepRegime 𝔍 s) T x with hr
  have hreg : stepRegime 𝔍 s T x := ⟨rfl, hsp⟩
  have hsplit : (head T r).append (tail T r) = T := head_append_tail T r
  have hT₀₁ : IsGeoTestTower (barMarked 𝔍) ((head T r).append (tail T r)) := by rw [hsplit]; exact hT
  have hD : ∀ {Y₃ : CMfd.{u} n} (T'' : BlowupTower X Y₃), T''.length ≤ T.length → IsGeoTestTower (barMarked 𝔍) T'' →
      IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T'' → HasLowerDataL R 𝔍 (lowerMarkedM 𝔍) T'' :=
    fun T'' _ hT'' hcan'' => hasLowerDataL_of_isCanonical 𝔍 R h𝔍 hd hn hmax hk T'' hT'' hcan''
  -- the lower data of `x`
  obtain ⟨hxW, hdom₀, hcan₀, hcos₀⟩ := hD T le_rfl hT hcan x hx hsp
  obtain ⟨hreg₀, hy₀⟩ := stepRegime_and_mem_cosupp_head 𝔍 h𝔍 T hT hx hsp
  have hTW := isGeoTestTower_of_isCanonical R hdom₀ _ hcan₀
  -- the open preimage of the mask
  set P : Opens Y := openPreimage (tail T r) (lowerMask 𝔍 s (head T r) ((tail T r).proj x)) with hP
  -- `R` is upper semicontinuous at `x` on the lower marked ideal
  have husc := R.usc _ hdom₀ _ hcan₀ ⟨x, hxW⟩ hcos₀
  have hev := eventually_forall_mem_of_eventually P hxW husc
  -- the value at `x`
  have hvx := stepOneInvM_eq_lower 𝔍 R h𝔍 hd hn hmax hk T hT hcan hD hx hreg rfl ⟨x, hxW⟩ hcos₀
  filter_upwards [hev, P.isOpen.mem_nhds hxW] with y hy hyP hyc
  have hyl : level 𝔍 T y ≤ s := by
    have h := level_le_of_mem_lowerMask 𝔍 hE (head T r) (tail T r) hreg₀.1 (q := y) hyP
    rwa [hsplit] at h
  rcases hyl.lt_or_eq with hlt | heq
  · exact (stepOneInvL_lt_of_level_lt R 𝔍 _ hlt).le
  · have hyc' : (⟨y, hyP⟩ : P) ∈ (geoTransformAlong (lowerMarkedM 𝔍 s (head T r) ((tail T r).proj x))
        (restrict (lowerMask 𝔍 s (head T r) ((tail T r).proj x)) (tail T r))).cosupp := by
      refine (mem_cosupp_lowerMarkedM_iff 𝔍 h𝔍 hd hn hmax (head T r) (tail T r) hT₀₁ hy₀ hreg₀.1 hxW hTW
        ⟨y, hyP⟩).mpr ⟨?_, ?_⟩
      · rw [hsplit]; exact hyc
      · rw [hsplit]; exact heq
    have hvy := stepOneInvM_eq_lower 𝔍 R h𝔍 hd hn hmax hk T hT hcan hD hx hreg rfl ⟨y, hyP⟩ hyc'
    rw [hvx, hvy, Prod.Lex.toLex_le_toLex]
    exact Or.inr ⟨rfl, WithTop.coe_le_coe.mpr (hy hyP hyc')⟩

/-- **Property (2) of the masked Step 1 value function** (`hir:step-one-usc`; the field `usc` of
`ResolutionInvariantExt.ResolutionInvariant`, with the canonical segment also a multiple test blow-up of `J̄`): for `𝔍` well
formed with `d ≥ 1`, of maximal order along `N` with `dim N ≤ k` (`0 < n`) and `R` a resolution invariant in dimension
`≤ k - 1`, along every multiple test blow-up `T` of `J̄` which is a canonical segment of `stepOneInvM R 𝔍`, the value
`stepOneInvM R 𝔍 T` is upper semicontinuous on the cosupport of `J̄_T`. -/
theorem stepOneInvM_usc (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T) :
    IsInvUSCOn (stepOneInvM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  intro x hx
  by_cases hsp : IsSpecial 𝔍 T x
  · filter_upwards [eventually_level_le 𝔍 hE T x] with y hy _
    exact stepOneInvL_le_of_isSpecial R 𝔍 _ hsp hy
  · exact stepOneInvM_eventually_le_of_not_isSpecial 𝔍 R h𝔍 hd hn hmax hk T hT hcan hx hsp

end USC

end

end Hironaka.StepOneUSC
