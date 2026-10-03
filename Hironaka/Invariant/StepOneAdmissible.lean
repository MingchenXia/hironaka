/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneUSC
import Hironaka.Invariant.StepOneAdmissibleTop
import Hironaka.Invariant.MemberRestrictAdmissible
import Hironaka.Invariant.ContactLowerValue
import Hironaka.Invariant.StepOneSpecialDrop
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantDriver
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantOrder
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneCanonicalTail
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.Invariant.StepOneRegime
import Hironaka.Invariant.StepOneValue
import Hironaka.Invariant.StepOneValueMasked
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1: admissibility of the level sets of the value

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 1a / 1b: near a non-special point
the centres of the canonical resolution of Step 1 are those of the canonical resolution of the restricted
lower-dimensional marked ideal, and its admissible centres are admissible centres of `J̄` (Lemma `le:S`).

Property (1) of the masked Step 1 value function (`hir:centre-function`, "admissibility of the level sets of the maximum, on
open sets") at the **non-special values** `(s, λ)`, `λ ∈ Λ`. Let `T` be a multiple test blow-up of `J̄` which is a canonical
segment of `stepOneInvM R 𝔍`, `W` an open set of its last stage on which the value is `≤ (s, λ)` on the cosupport, and `x` a
point of `W` in the cosupport.

* If the value of `x` is not `(s, λ)`, a neighbourhood of `x` misses the level set: the cosupport is closed, and by upper
  semicontinuity (`StepOneUSC.stepOneInvM_usc`) the values near a point of value `< (s, λ)` stay below `(s, λ)`
  (`exists_opens_preimage_eq_empty`).
* If the value of `x` is `(s, λ)`, `x` is not special, of level `s`, and has lower data (the canonical-tail theorem): a mask `W_x`
  at the start of its run, the lower marked ideal `𝔏` on it, and the restricted tail `T₁|_{W_x}`, a canonical segment of `𝔏`.
  On `V = W ∩ T₁⁻¹ W_x` the level set is the level set `{R = λ}` of the lower invariant on the cosupport of `𝔏` along
  `T₁|_{W_x}` (`StepOneCanonicalTail.stepOneInvM_eq_lower`), on which `R ≤ λ`; the field `admissible` of `R` makes it an
  admissible centre of the restriction of the transform of `𝔏`, and the **transfer** (`AdmissibleTransfer`) makes it one of
  the restriction of `J̄_T` (`exists_opens_isAdmissibleCentre_of_eq`).
* Admissible centres are local relative to an open set
  (`MaxLocusLocal.isAdmissibleCentre_pullback_val_of_forall_exists_opens`).

The transfer is Włodarczyk's `le:S` for one centre, on every open set of the last stage: for `s ≥ 1`
`MemberRestrictAdmissible.isAdmissibleCentre_pullback_val_of_lowerMarked_succ` (`hasAdmissibleTransfer_succ`), for
`s = 0` `ContactLowerValue.isAdmissibleCentre_of_lowerMarkedM_zero` (`hasAdmissibleTransfer_zero`; the divisor is
kept and masked). With the top values (`StepOneAdmissibleTop`) this is property (1) at every value; at the maximum
value on the whole last stage it makes the maximum locus an admissible centre, so **canonical segments of
`stepOneInvM R 𝔍` are multiple test blow-ups of `J̄`**, and the test-tower hypothesis of the canonical-tail theorem
and of properties (1)--(4) is removed.

## Main results

* `AdmissibleTransfer`, `HasAdmissibleTransfer`, `hasAdmissibleTransfer_succ`, `hasAdmissibleTransfer_zero`,
  `hasAdmissibleTransfer`;
* `exists_opens_preimage_eq_empty`, `exists_opens_isAdmissibleCentre_of_eq`;
* `stepOneInvM_admissible_coe_of_hasAdmissibleTransfer`: the level sets of the values `(s, λ)`, given the transfer at level `s`;
* `stepOneInvM_admissible_coe`, **`stepOneInvM_admissible`**: property (1) at the values `(s + 1, λ)`, `(s, λ)`, and
  at every value;
* `isAdmissibleCentre_maxLocus_stepOneInvM`, **`isGeoTestTower_of_isCanonical_stepOneInvM`**: the maximum locus is an
  admissible centre, and canonical segments are multiple test blow-ups;
* `stepOneInvM_admissible_of_isCanonical`, `stepOneInvM_usc_of_isCanonical`, `stepOneInvM_decrease_of_isCanonical`,
  `stepOneInvM_emptyStep_of_isCanonical`: the canonical-tail theorem and properties (1)--(4) along canonical
  segments, without the test-tower hypothesis (the shapes of the fields `admissible`, `usc`, `decrease`, `emptyStep`
  of `ResolutionInvariantExt.ResolutionInvariant`, `IsInvDomain` replaced by the explicit hypotheses: well formed,
  `d ≥ 1`, maximal order along `N`, `dim N ≤ k`, `0 < n`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneAdmissible

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime Hironaka.StepOneValue Hironaka.StepOneLowerDomain Hironaka.StepOneMaskTower Hironaka.StepOneValueMasked Hironaka.StepOneCanonicalTail Hironaka.StepOneUSC Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen Hironaka.HomogenizedIdealAlong Hironaka.ResolutionInvariantOrder Hironaka.MaxLocusLocal
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ}

/-! ### The transfer of admissible centres from the lower marked ideal -/

section Transfer

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **The transfer of admissible centres at level `s`** for the split `T₀ T₁` and the point `y₀` of the stage of `T₀`: on every
open set `W''` of the last stage of the restricted tail `T₁|_W` (`W` the mask of `y₀`), an admissible centre of the restriction
of the transform of the masked lower marked ideal is an admissible centre of the restriction of `J̄_{T₀ T₁}`. -/
def AdmissibleTransfer (s : ℕ) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (y₀ : Y₀) : Prop :=
  ∀ (W'' : Opens (openPreimage T₁ (lowerMask 𝔍 s T₀ y₀))) (C : Set W''),
    (MarkedIdeal.pullback (Subtype.val : W'' → openPreimage T₁ (lowerMask 𝔍 s T₀ y₀))
      (geoTransformAlong (lowerMarkedM 𝔍 s T₀ y₀) (restrict (lowerMask 𝔍 s T₀ y₀) T₁))).IsAdmissibleCentre C →
    (MarkedIdeal.pullback (Subtype.val : W'' → openPreimage T₁ (lowerMask 𝔍 s T₀ y₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₁ (lowerMask 𝔍 s T₀ y₀) → Y)
        (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)))).IsAdmissibleCentre C

/-- **The transfer holds at level `s`** along every multiple test blow-up `T₀ T₁` of `J̄`, for every point `y₀` of its own mask
along whose restricted tail `T₁|_W` is a multiple test blow-up of the lower marked ideal. -/
def HasAdmissibleTransfer (s : ℕ) : Prop :=
  ∀ {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y),
    IsGeoTestTower (barMarked 𝔍) (T₀.append T₁) → ∀ y₀ : Y₀, y₀ ∈ lowerMask 𝔍 s T₀ y₀ →
      IsGeoTestTower (lowerMarkedM 𝔍 s T₀ y₀) (restrict (lowerMask 𝔍 s T₀ y₀) T₁) →
        AdmissibleTransfer 𝔍 s T₀ T₁ y₀

/-- **Step 1ab: the transfer holds at every level `s + 1`** (Włodarczyk `le:S` for one centre;
`MemberRestrictAdmissible.isAdmissibleCentre_pullback_val_of_lowerMarked_succ`). -/
theorem hasAdmissibleTransfer_succ (h𝔍 : 𝔍.IsWellFormed) (hn : 0 < n) (s : ℕ) :
    HasAdmissibleTransfer 𝔍 (s + 1) :=
  fun T₀ T₁ hT _ hy₀ hTW W'' _ h =>
    MemberRestrictAdmissible.isAdmissibleCentre_pullback_val_of_lowerMarked_succ 𝔍 h𝔍 hn T₀ T₁ hT hy₀ hTW W'' h

/-- **Step 1bb: the transfer holds at level `0`** (the divisor is kept and masked;
`ContactLowerValue.isAdmissibleCentre_of_lowerMarkedM_zero`). -/
theorem hasAdmissibleTransfer_zero (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) : HasAdmissibleTransfer 𝔍 0 :=
  fun T₀ T₁ hT _ hy₀ _ W'' C h => ContactLowerValue.isAdmissibleCentre_of_lowerMarkedM_zero 𝔍 h𝔍 hd T₀ T₁ hT hy₀ W'' C h

/-- **The transfer holds at every level.** -/
theorem hasAdmissibleTransfer (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n) :
    ∀ s : ℕ, HasAdmissibleTransfer 𝔍 s
  | 0 => hasAdmissibleTransfer_zero 𝔍 h𝔍 hd
  | s + 1 => hasAdmissibleTransfer_succ 𝔍 h𝔍 hn s

end Transfer

/-! ### The level sets near a point -/

section Local

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **A point off the level set has a neighbourhood missing it**: along a multiple test blow-up `T` of `J̄` which is a
canonical segment of `stepOneInvM R 𝔍`, on an open `W` on which the value is `≤ l` on the cosupport, a point `x ∈ W` which is
not in the cosupport or has a value `≠ l` has an open neighbourhood `V ⊆ W` on which the level set `{value = l}` is empty (the
cosupport is closed; upper semicontinuity). -/
theorem exists_opens_preimage_eq_empty (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T) (W : Opens Y)
    (l : ℕ ×ₗ WithTop Λ)
    (hle : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W → stepOneInvM R 𝔍 T y ≤ l) {x : Y}
    (hxW : x ∈ W) (hx : ¬ (x ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧ stepOneInvM R 𝔍 T x = l)) :
    ∃ V : Opens Y, x ∈ V ∧ V ≤ W ∧
      (Subtype.val : V → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧ stepOneInvM R 𝔍 T y = l} = ∅ := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T hT
  -- an open neighbourhood `t` of `x` missing the level set
  obtain ⟨t, hto, hxt, hdisj⟩ : ∃ t : Set Y, IsOpen t ∧ x ∈ t ∧ ∀ y ∈ t,
      ¬ (y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧ stepOneInvM R 𝔍 T y = l) := by
    by_cases hxc : x ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp
    · have hxl : stepOneInvM R 𝔍 T x < l := lt_of_le_of_ne (hle x hxc hxW) fun h => hx ⟨hxc, h⟩
      obtain ⟨t, hts, hto, hxt⟩ := mem_nhds_iff.mp (stepOneInvM_usc 𝔍 R h𝔍 hd hn hmax hk T hT hcan x hxc)
      exact ⟨t, hto, hxt, fun y hy hyl => absurd hyl.2 (((hts hy) hyl.1).trans_lt hxl).ne⟩
    · have hcl : IsClosed (geoTransformAlong (barMarked 𝔍) T).cosupp :=
        GiraudAlong.isClosed_cosupport_along hwf.isCoherent hwf.isClosedSubmanifold_N _
      exact ⟨_, hcl.isOpen_compl, hxc, fun y hy hyl => hy hyl.1⟩
  refine ⟨W ⊓ ⟨t, hto⟩, ⟨hxW, hxt⟩, inf_le_left, ?_⟩
  exact eq_empty_iff_forall_notMem.mpr fun v hv => hdisj v v.2.2 hv

/-- **Near a point of the level set of a non-special value** `(s, λ)`, `s` the level of the point, the level set is an
admissible centre, given the transfer at level `s`: on `V = W ∩ T₁⁻¹ W_x` it is the level set `{R = λ}` of the lower invariant
on the cosupport of the lower marked ideal of `x` (`stepOneInvM_eq_lower`), admissible for the restriction of its transform by
the field `admissible` of `R` (on `V`, `R ≤ λ` there), hence admissible for the restriction of `J̄_T` by the transfer. -/
theorem exists_opens_isAdmissibleCentre_of_eq (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T) (W : Opens Y)
    {x : Y} (l : Λ)
    (htr : HasAdmissibleTransfer 𝔍 (level 𝔍 T x))
    (hle : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W →
      stepOneInvM R 𝔍 T y ≤ toLex (level 𝔍 T x, (l : WithTop Λ)))
    (hxW : x ∈ W) (hx : x ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) (hsp : ¬ IsSpecial 𝔍 T x) :
    ∃ V : Opens Y, x ∈ V ∧ V ≤ W ∧
      (MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong (barMarked 𝔍) T)).IsAdmissibleCentre
        ((Subtype.val : V → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
          stepOneInvM R 𝔍 T y = toLex (level 𝔍 T x, (l : WithTop Λ))}) := by
  set s := level 𝔍 T x with hs
  set r := regimeRun (stepRegime 𝔍 s) T x with hr
  have hreg : stepRegime 𝔍 s T x := ⟨rfl, hsp⟩
  have hsplit : (head T r).append (tail T r) = T := head_append_tail T r
  have hT₀₁ : IsGeoTestTower (barMarked 𝔍) ((head T r).append (tail T r)) := by rw [hsplit]; exact hT
  have hD : ∀ {Y₃ : CMfd.{u} n} (T'' : BlowupTower X Y₃), T''.length ≤ T.length → IsGeoTestTower (barMarked 𝔍) T'' →
      IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T'' → HasLowerDataL R 𝔍 (lowerMarkedM 𝔍) T'' :=
    fun T'' _ hT'' hcan'' => hasLowerDataL_of_isCanonical 𝔍 R h𝔍 hd hn hmax hk T'' hT'' hcan''
  -- the lower data of `x`
  obtain ⟨hxM, hdom₀, hcan₀, -⟩ := hD T le_rfl hT hcan x hx hsp
  obtain ⟨hreg₀, hy₀⟩ := stepRegime_and_mem_cosupp_head 𝔍 h𝔍 T hT hx hsp
  have hTW := isGeoTestTower_of_isCanonical R hdom₀ _ hcan₀
  -- the neighbourhood
  set P : Opens Y := openPreimage (tail T r) (lowerMask 𝔍 s (head T r) ((tail T r).proj x)) with hP
  have hVP : W ⊓ P ≤ P := inf_le_right
  refine ⟨W ⊓ P, ⟨hxW, hxM⟩, inf_le_left, ?_⟩
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T hT
  have hVc : (MarkedIdeal.pullback (Subtype.val : (W ⊓ P : Opens Y) → Y) (geoTransformAlong (barMarked 𝔍) T)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcT
  -- the cosupport of the lower marked ideal along the restricted tail, and the values there
  have hcos : ∀ q : P, q ∈ (geoTransformAlong (lowerMarkedM 𝔍 s (head T r) ((tail T r).proj x))
      (restrict (lowerMask 𝔍 s (head T r) ((tail T r).proj x)) (tail T r))).cosupp ↔
        (q : Y) ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧ level 𝔍 T q = s := by
    intro q
    rw [mem_cosupp_lowerMarkedM_iff 𝔍 h𝔍 hd hn hmax (head T r) (tail T r) hT₀₁ hy₀ hreg₀.1 hxM hTW q, hsplit]
  -- `R ≤ λ` on the cosupport over `W ∩ P`
  have hle'' : ∀ q ∈ (geoTransformAlong (lowerMarkedM 𝔍 s (head T r) ((tail T r).proj x))
      (restrict (lowerMask 𝔍 s (head T r) ((tail T r).proj x)) (tail T r))).cosupp,
        q ∈ nestedOpens P (W ⊓ P) →
        R.inv (lowerMarkedM 𝔍 s (head T r) ((tail T r).proj x))
          (restrict (lowerMask 𝔍 s (head T r) ((tail T r).proj x)) (tail T r)) q ≤ l := by
    intro q hq hqV
    have hv := stepOneInvM_eq_lower 𝔍 R h𝔍 hd hn hmax hk T hT hcan hD hx hreg rfl q hq
    have h := hle q ((hcos q).mp hq).1 hqV.1
    rw [hv, Prod.Lex.toLex_le_toLex] at h
    rcases h with h | ⟨-, h⟩
    · exact absurd h (lt_irrefl _)
    · exact WithTop.coe_le_coe.mp h
  -- the field `admissible` of `R` on `W ∩ P`, then the transfer
  have hadm := R.admissible _ hdom₀ _ hcan₀ (nestedOpens P (W ⊓ P)) l hle''
  have htr' := htr (head T r) (tail T r) hT₀₁ _ hxM hTW (nestedOpens P (W ⊓ P)) _ hadm
  rw [show (head T r).append (tail T r) = T from hsplit, pullback_val_pullback_val hcT hVP] at htr'
  -- the two level sets agree
  have hset : (Subtype.val : nestedOpens P (W ⊓ P) → P) ⁻¹'
      {q | q ∈ (geoTransformAlong (lowerMarkedM 𝔍 s (head T r) ((tail T r).proj x))
          (restrict (lowerMask 𝔍 s (head T r) ((tail T r).proj x)) (tail T r))).cosupp ∧
        R.inv (lowerMarkedM 𝔍 s (head T r) ((tail T r).proj x))
          (restrict (lowerMask 𝔍 s (head T r) ((tail T r).proj x)) (tail T r)) q = l} =
      (nestedOpensDiffeo (n := n) hVP) ⁻¹' ((Subtype.val : (W ⊓ P : Opens Y) → Y) ⁻¹'
        {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧ stepOneInvM R 𝔍 T y = toLex (s, (l : WithTop Λ))}) := by
    ext w
    simp only [mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨hq, hql⟩
      refine ⟨((hcos _).mp hq).1, ?_⟩
      have hv := stepOneInvM_eq_lower 𝔍 R h𝔍 hd hn hmax hk T hT hcan hD hx hreg rfl _ hq
      rw [hql] at hv
      exact hv
    · rintro ⟨hc, hv⟩
      replace hc : ((w : P) : Y) ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp := hc
      replace hv : stepOneInvM R 𝔍 T ((w : P) : Y) = toLex (s, (l : WithTop Λ)) := hv
      have hlev : level 𝔍 T ((w : P) : Y) = s := by
        have h := congrArg (fun p => (ofLex p).1) hv
        simp only [ofLex_toLex] at h
        rw [← h]
        exact (stepOneInvL_fst R 𝔍 _ T _).symm
      have hq := (hcos (w : P)).mpr ⟨hc, hlev⟩
      refine ⟨hq, ?_⟩
      rw [stepOneInvM_eq_lower 𝔍 R h𝔍 hd hn hmax hk T hT hcan hD hx hreg rfl _ hq] at hv
      have h := congrArg (fun p => (ofLex p).2) hv
      simp only [ofLex_toLex] at h
      exact WithTop.coe_injective h
  rw [hset] at htr'
  exact (MarkedIdealTowerTransport.isAdmissibleCentre_pullback_iff (Φ := nestedOpensDiffeo (n := n) hVP) hVc).mp htr'

end Local

/-! ### Property (1) at the non-special values -/

section Admissible

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **Property (1) at the values `(s, λ)`, given the transfer at level `s`**: along a multiple test blow-up `T` of `J̄` which is a
canonical segment of `stepOneInvM R 𝔍`, on an open `W` on which the value is `≤ (s, λ)` on the cosupport, the points of `W` in
the cosupport with value `(s, λ)` form an admissible centre of the restriction of `J̄_T` to `W` (glued from
`exists_opens_isAdmissibleCentre_of_eq` and `exists_opens_preimage_eq_empty`). -/
theorem stepOneInvM_admissible_coe_of_hasAdmissibleTransfer (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T) (W : Opens Y)
    (s : ℕ) (l : Λ) (htr : HasAdmissibleTransfer 𝔍 s)
    (hle : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W →
      stepOneInvM R 𝔍 T y ≤ toLex (s, (l : WithTop Λ))) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        stepOneInvM R 𝔍 T y = toLex (s, (l : WithTop Λ))}) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T hT
  refine isAdmissibleCentre_pullback_val_of_forall_exists_opens hcT W fun x hxW => ?_
  by_cases hx : x ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧ stepOneInvM R 𝔍 T x = toLex (s, (l : WithTop Λ))
  · obtain ⟨hxc, hxv⟩ := hx
    -- `x` is not special, of level `s`
    have hsp : ¬ IsSpecial 𝔍 T x := fun h => by
      have hxv' : stepOneInvL R 𝔍 (lowerMarkedM 𝔍) T x = toLex (s, (l : WithTop Λ)) := hxv
      rw [stepOneInvL_of_isSpecial R 𝔍 _ T h] at hxv'
      have := congrArg (fun p => (ofLex p).2) hxv'
      simp only [ofLex_toLex] at this
      exact WithTop.top_ne_coe this
    have hlev : level 𝔍 T x = s := by
      have h := congrArg (fun p => (ofLex p).1) hxv
      simp only [ofLex_toLex] at h
      rw [← h]
      exact (stepOneInvL_fst R 𝔍 _ T x).symm
    subst hlev
    exact exists_opens_isAdmissibleCentre_of_eq 𝔍 R h𝔍 hd hn hmax hk T hT hcan W l htr hle hxW hxc hsp
  · obtain ⟨V, hxV, hVW, hV⟩ := exists_opens_preimage_eq_empty 𝔍 R h𝔍 hd hn hmax hk T hT hcan W _ hle hxW hx
    refine ⟨V, hxV, hVW, ?_⟩
    rw [hV]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- **Property (1) of the masked Step 1 value at the values `(s, λ)`** (`hir:step-one-admissible`; Step 1ab for `s ≥ 1`,
Step 1bb for `s = 0`). -/
theorem stepOneInvM_admissible_coe (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T) (W : Opens Y)
    (s : ℕ) (l : Λ)
    (hle : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W →
      stepOneInvM R 𝔍 T y ≤ toLex (s, (l : WithTop Λ))) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        stepOneInvM R 𝔍 T y = toLex (s, (l : WithTop Λ))}) :=
  stepOneInvM_admissible_coe_of_hasAdmissibleTransfer 𝔍 R h𝔍 hd hn hmax hk T hT hcan W s l
    (hasAdmissibleTransfer 𝔍 h𝔍 hd hn s) hle

/-- **Property (1) of the masked Step 1 value function at every value** (`hir:step-one-admissible`; the field `admissible` of
`ResolutionInvariantExt.ResolutionInvariant`, with the canonical segment also a multiple test blow-up of `J̄`): the values
`(s, ∞)` by `StepOneAdmissibleTop.stepOneInvL_admissible_top`, the values `(s, λ)` by `stepOneInvM_admissible_coe`. -/
theorem stepOneInvM_admissible (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T) (W : Opens Y)
    (l : ℕ ×ₗ WithTop Λ)
    (hle : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W → stepOneInvM R 𝔍 T y ≤ l) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧ stepOneInvM R 𝔍 T y = l}) := by
  obtain ⟨⟨s, t⟩, rfl⟩ : ∃ p : ℕ × WithTop Λ, toLex p = l := ⟨ofLex l, toLex_ofLex l⟩
  induction t using WithTop.recTopCoe with
  | top => exact StepOneAdmissibleTop.stepOneInvL_admissible_top R 𝔍 _ h𝔍 hd hn hmax T hT W s hle
  | coe l => exact stepOneInvM_admissible_coe 𝔍 R h𝔍 hd hn hmax hk T hT hcan W s l hle

/-- **The maximum locus is an admissible centre** of `J̄_T` along a multiple test blow-up which is a canonical segment of
`stepOneInvM R 𝔍` (property (1) on the whole last stage, at the maximum value). -/
theorem isAdmissibleCentre_maxLocus_stepOneInvM (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T) :
    (geoTransformAlong (barMarked 𝔍) T).IsAdmissibleCentre
      (maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp) := by
  by_cases hne : (maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hadm := stepOneInvM_admissible 𝔍 R h𝔍 hd hn hmax hk T hT hcan ⊤ (stepOneInvM R 𝔍 T y₀)
      (fun y hy _ => hy₀.2 y hy)
    rw [← ResolutionInvariantDriver.maxLocus_eq_level hy₀] at hadm
    have hJ := isWellFormed_barMarked 𝔍 h𝔍
    obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T hT
    exact ResolutionInvariantDriver.isAdmissibleCentre_of_pullback_val_top
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) hadm
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- **Canonical segments of the masked Step 1 value are multiple test blow-ups of `J̄`** (induction on the length: each
centre is empty or the maximum locus, an admissible centre by `isAdmissibleCentre_maxLocus_stepOneInvM`). -/
theorem isGeoTestTower_of_isCanonical_stepOneInvM (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T →
      IsGeoTestTower (barMarked 𝔍) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      obtain ⟨hcanT, hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T ∧
          (C = ∅ ∨ C = maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp) := hcan
      have hTt := isGeoTestTower_of_isCanonical_stepOneInvM h𝔍 hd hn hmax hk T hcanT
      refine (isGeoTestTower_step_iff _ T C π hπ).mpr ⟨hTt, ?_⟩
      rcases hC with rfl | rfl
      · exact MarkedIdeal.isAdmissibleCentre_empty _
      · exact isAdmissibleCentre_maxLocus_stepOneInvM 𝔍 R h𝔍 hd hn hmax hk T hTt hcanT

end Admissible

/-! ### Along canonical segments: the test-tower hypothesis removed -/

section Canonical

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **Property (1) along canonical segments** (the field `admissible`, `IsInvDomain` replaced by the explicit hypotheses). -/
theorem stepOneInvM_admissible_of_isCanonical (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T) (W : Opens Y) (l : ℕ ×ₗ WithTop Λ)
    (hle : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W → stepOneInvM R 𝔍 T y ≤ l) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧ stepOneInvM R 𝔍 T y = l}) :=
  stepOneInvM_admissible 𝔍 R h𝔍 hd hn hmax hk T (isGeoTestTower_of_isCanonical_stepOneInvM 𝔍 R h𝔍 hd hn hmax hk T hcan)
    hcan W l hle

/-- **Property (2) along canonical segments** (the field `usc`). -/
theorem stepOneInvM_usc_of_isCanonical (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T) :
    IsInvUSCOn (stepOneInvM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp :=
  stepOneInvM_usc 𝔍 R h𝔍 hd hn hmax hk T (isGeoTestTower_of_isCanonical_stepOneInvM 𝔍 R h𝔍 hd hn hmax hk T hcan) hcan

/-- **Property (3) along canonical segments** (the field `decrease`; `C ≠ ∅` is not needed). -/
theorem stepOneInvM_decrease_of_isCanonical (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y Z : CMfd.{u} n} (T : BlowupTower X Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T)
    (hC : C = maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp) :
    ∀ z ∈ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp,
      (π z ∈ C → stepOneInvM R 𝔍 (.step T C π hπ) z < stepOneInvM R 𝔍 T (π z)) ∧
      (π z ∉ C → stepOneInvM R 𝔍 (.step T C π hπ) z = stepOneInvM R 𝔍 T (π z)) :=
  StepOneSpecialDrop.stepOneInvM_decrease R 𝔍 h𝔍 hd hn hmax hk T C π hπ
    (isGeoTestTower_of_isCanonical_stepOneInvM 𝔍 R h𝔍 hd hn hmax hk (.step T C π hπ)
      (⟨hcan, Or.inr hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T ∧
        (C = ∅ ∨ C = maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp)))
    hcan hC

/-- **Property (4) along canonical segments** (the field `emptyStep`). -/
theorem stepOneInvM_emptyStep_of_isCanonical (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y Z : CMfd.{u} n} (T : BlowupTower X Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) (hC : C = ∅)
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T) :
    ∀ z ∈ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp,
      stepOneInvM R 𝔍 (.step T C π hπ) z = stepOneInvM R 𝔍 T (π z) :=
  StepOneSpecialDrop.stepOneInvM_emptyStep R 𝔍 h𝔍 hd hn hmax hk T C π hπ hC
    (isGeoTestTower_of_isCanonical_stepOneInvM 𝔍 R h𝔍 hd hn hmax hk T hcan) hcan

end Canonical

end

end Hironaka.StepOneAdmissible
