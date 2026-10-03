/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneValueMasked
import Hironaka.Invariant.InvDomainRebase
import Hironaka.Invariant.ContactStageRebase
import Hironaka.MarkedIdeal.CoefficientIdealAlongRestrictionDrop
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.BoundaryCount
import Hironaka.MarkedIdeal.CodimOneSupportAlong
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Invariant.ContactCanonicalAlong
import Hironaka.Invariant.ContactIndependenceAlong
import Hironaka.Invariant.ContactStageTail
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Invariant.InvDomainMemberRestriction
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.Invariant.StepOneMaskTower
import Hironaka.Invariant.StepOneNearby
import Hironaka.Invariant.StepOneValue
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1: the value of a nearby point through the reference point's lower marked ideal

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 1 (the restrictions `J̄_{|H^s_α}`
in Step 1a, `J̄_{|V(u)}` in Step 1b, computed along the part of the resolution after they are formed) and the lemma
on the commutativity of the resolution procedure with étale morphisms.

Let `T = T₀' M T₁` be a multiple test blow-up of `J̄ = 𝓒_N(𝓗_N(𝔍))`, `y₀` a point of the last stage of `T₀ = T₀' M` in the regime
of level `s`, with mask `W` and lower marked ideal `𝓢(y₀)` (the masked family `StepOneValueMasked.lowerMarkedM`), and `p` a point
of the last stage over `W` whose own split is at `T₀'` (it entered the regime earlier), with lower data there, and such that the
steps of `M` are empty over its mask `W'` (`StepOneValueMasked.centresAvoid_lowerMaskL`).  The value of `p` is computed from
`𝓢(p₁)|_{W'}` along `(M T₁)|_{W'}`; this module moves it to the stage `T₀`:

* `inv_restrict_append`: `(M T₁)|_{W'}` is isomorphic to `M|_{W'}` followed by `T₁|_{M⁻¹W'}`
  (`isTowerIso_restrict_append`), so canonical segments, cosupports and values pass between the two (property (6)
  over the identity);
* `memberRestrict_membersThrough_congr`: Step 1ab's restricted marked ideal depends only on the members through the point;
* **`lowerValue_eq_succ`** (Step 1ab, `s ≥ 1`): re-basing along `M` (`InvDomainRebase.memberRestrict_rebase`), then
  the restricted marked ideal formed at `T₀` at the image of `p` is the one formed at `y₀` (same original members
  through the two points), and the values on the two open sets `M⁻¹W'` and `W` agree
  (`StepOneNearby.inv_eq_of_two_opens`): the lower value of `p` is `R` of `𝓢(y₀)|_W` along `T₁|_W` at `p`;
* `contactKept`, `contactKept_rebase`, **`lowerValue_eq_zero_rebase`** (Step 1bb, `s = 0`, original members kept):
  re-basing along `M` (`restrictEquiv_restrictedCoeffHomAlong_rebase`, any divisor, with `inv_rebase`) -- the lower
  value of `p` is `R` of `contactKept 𝔍 v (T₀' M) (M⁻¹W')` along `T₁|_{M⁻¹W'}`, `v` the tangent direction chosen at
  the base point of `p`; the change to the tangent direction of `y₀` is `StepOneTangentChange`;
* the cosupports of the lower marked ideals along restricted tails: `mem_cosupp_lowerMarked_succ_iff` (Step 1ab: the
  points of the cosupport of `J̄_T` on the strict transforms of the original members through `y₀`;
  `CoefficientIdealAlongRestrictionDrop.coeffAlong_restrict_withE_iff` and `strictAlong_inter_memberInter`),
  `level_eq_iff_of_mem_maskA` (over the mask those are the points of level `s`),
  `isGeoTestTower_cosupp_lowerMarkedB` (Step 1bb: the restricted tail is a multiple test blow-up and the cosupport
  is the trace of `cosupp J̄_T`, `ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneCompare

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime Hironaka.StepOneValue Hironaka.StepOneLowerDomain Hironaka.StepOneMaskTower Hironaka.StepOneNearby Hironaka.BoundaryCount Hironaka.InvDomainMemberRestriction Hironaka.MarkedIdealBiholomorphism Hironaka.BlowupTowerIsomorphism Hironaka.RestrictEmptyTower Hironaka.MarkedIdealRestrictOpen Hironaka.HomogenizedIdealAlong Hironaka.MaximalOrderStepOneB Hironaka.TangentDirectionAlong Hironaka.StepOneValueMasked Hironaka.CoefficientIdealRestriction
open Hironaka.HomogenizedGlueingTower (strictAlong strictAlong_restrict)
open Hironaka.BlowupTowerIsoTail (opensCongr isTowerIso_restrict_append openPreimage_append)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isGeoTestTower_of_isCanonical IsEmptyTower)

noncomputable section

variable {n : ℕ}

/-! ### Two generic tools -/

section Generic

variable {Λ : Type v} [LinearOrder Λ] {k : ℕ}

/-- **Canonical segments and values along a restricted concatenation**: for an open `W` of `Y₁`, a marked ideal `𝔪` on
`W` in the domain of `R` and towers `M`, `T₁`, if `(M T₁)|_W` is a canonical segment of `𝔪`, so is `M|_W` followed
by `T₁|_{M⁻¹W}`, and at the points of the cosupport the values agree (`isTowerIso_restrict_append`, property (6)
over the identity of `W`). -/
theorem inv_restrict_append (R : ResolutionInvariant.{u, v} n k Λ) {Y₁ Y₀ Y : CMfd.{u} n} (W : Opens Y₁)
    {𝔪 : MarkedIdeal n (CMfd.of (n := n) W)} (hdom : IsInvDomain k 𝔪) (M : BlowupTower Y₁ Y₀)
    (T₁ : BlowupTower Y₀ Y) (hcan : IsCanonical 𝔪 (R.inv 𝔪) (restrict W (M.append T₁))) :
    IsCanonical 𝔪 (R.inv 𝔪) ((restrict W M).append (restrict (openPreimage M W) T₁)) ∧
      ∀ (p : Y) (h : p ∈ openPreimage (M.append T₁) W) (h' : p ∈ openPreimage T₁ (openPreimage M W)),
        (⟨p, h⟩ : openPreimage (M.append T₁) W) ∈ (geoTransformAlong 𝔪 (restrict W (M.append T₁))).cosupp →
        (⟨p, h'⟩ : openPreimage T₁ (openPreimage M W)) ∈
            (geoTransformAlong 𝔪 ((restrict W M).append (restrict (openPreimage M W) T₁))).cosupp ∧
          R.inv 𝔪 ((restrict W M).append (restrict (openPreimage M W) T₁)) ⟨p, h'⟩ =
            R.inv 𝔪 (restrict W (M.append T₁)) ⟨p, h⟩ := by
  have hiso := (isTowerIso_restrict_append W M T₁).symm
  have hpb : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) W) ∞).symm 𝔪 = 𝔪 :=
    ContactCanonicalAlong.pullback_id 𝔪 hdom.isWellFormed.isCoherent
  have hcan' := ResolutionInvariantExt.isCanonical_of_isTowerIso R hdom _ hiso hcan
  rw [hpb] at hcan'
  refine ⟨hcan', fun p h h' hp => ?_⟩
  have hTt := isGeoTestTower_of_isCanonical R hdom _ hcan
  have hcos := IsTowerIso.cosupp_geoTransformAlong _ hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent hiso hTt
  rw [hpb] at hcos
  have hχ : (opensCongr (n := n) (openPreimage_append M T₁ W).symm).symm ⟨p, h'⟩ = ⟨p, h⟩ := Subtype.ext rfl
  have hp' : (⟨p, h'⟩ : openPreimage T₁ (openPreimage M W)) ∈
      (geoTransformAlong 𝔪 ((restrict W M).append (restrict (openPreimage M W) T₁))).cosupp := by
    rw [hcos, mem_preimage, hχ]
    exact hp
  refine ⟨hp', ?_⟩
  have key := R.towerIso _ 𝔪 hdom _ _ _ hiso hcan ⟨p, h'⟩ (by rw [hχ]; exact hp)
  rw [hpb, hχ] at key
  exact key

/-- **Step 1ab's restricted marked ideal depends only on the members of `E₀` through the point.** -/
theorem memberRestrict_membersThrough_congr {Y : CMfd.{u} n} {𝔪 𝔪' : MarkedIdeal n Y} (h : 𝔪 = 𝔪')
    {E₀ E₀' : List (Set Y)} (hE : E₀ = E₀') {y y' : Y} (hy : ∀ H ∈ E₀', y ∈ H ↔ y' ∈ H) :
    memberRestrict 𝔪 (membersThrough 𝔪.E E₀ y) = memberRestrict 𝔪' (membersThrough 𝔪'.E E₀' y') := by
  subst h hE
  congr 1
  ext i
  rw [mem_membersThrough, mem_membersThrough]
  exact and_congr_right fun hi => hy _ hi

end Generic

/-! ### Step 1ab: the comparison -/

section Succ

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ} (R : ResolutionInvariant.{u, v} n k Λ)
  (𝔍 : MarkedIdeal n X)

/-- **The lower value of a nearby point, Step 1ab** (`hir:step-one-compare`, `s ≥ 1`, masked family `lowerMarkedM`, which is
`StepOneValue.lowerMarked` at these levels): let `T₀' M T₁` be a multiple test
blow-up of `J̄` (`𝔍` well formed, `d ≥ 1`, `0 < n`), `y₀` a point of the last stage of `T₀ = T₀' M` of level `s + 1` whose
lower marked ideal `𝓢(y₀)|_W` lies in the domain of `R` with `T₁|_W` a canonical segment of it, and `p` a point of the last
stage over `W`, whose image at `T₀` has the level of `y₀`,, lying in the cosupport of `𝓢(y₀)|_W` along `T₁|_W`.  If `p` has
lower data at the split `T₀' (M T₁)` and the centres of `M` miss its mask `W'`, its lower value is the value of `R` for
`𝓢(y₀)|_W` along `T₁|_W` at `p`. -/
theorem lowerValue_eq_succ (h𝔍 : 𝔍.IsWellFormed) (hn : 0 < n) {s : ℕ} {Y₁ Y₀ Y : CMfd.{u} n}
    (T₀' : BlowupTower X Y₁) (M : BlowupTower Y₁ Y₀) (T₁ : BlowupTower Y₀ Y)
    (hT : IsGeoTestTower (barMarked 𝔍) ((T₀'.append M).append T₁)) {y₀ : Y₀}
    (hdom₀ : IsInvDomain k (lowerMarkedM 𝔍 (s + 1) (T₀'.append M) y₀))
    (hcan₀ : IsCanonical (lowerMarkedM 𝔍 (s + 1) (T₀'.append M) y₀)
      (R.inv (lowerMarkedM 𝔍 (s + 1) (T₀'.append M) y₀)) (restrict (lowerMask 𝔍 (s + 1) (T₀'.append M) y₀) T₁))
    {p : Y} (hpW : T₁.proj p ∈ lowerMask 𝔍 (s + 1) (T₀'.append M) y₀)
    (hlp : level 𝔍 (T₀'.append M) (T₁.proj p) = level 𝔍 (T₀'.append M) y₀)
    (hcos₀ : (⟨p, hpW⟩ : openPreimage T₁ (lowerMask 𝔍 (s + 1) (T₀'.append M) y₀)) ∈
      (geoTransformAlong (lowerMarkedM 𝔍 (s + 1) (T₀'.append M) y₀)
        (restrict (lowerMask 𝔍 (s + 1) (T₀'.append M) y₀) T₁)).cosupp)
    (hd₁ : LowerDataL R 𝔍 (lowerMarkedM 𝔍) (s + 1) T₀' (M.append T₁) p)
    (hM : CentresAvoid (lowerMask 𝔍 (s + 1) T₀' ((M.append T₁).proj p)) M) :
    lowerValueL R 𝔍 (lowerMarkedM 𝔍) (s + 1) T₀' (M.append T₁) p =
      ((R.inv (lowerMarkedM 𝔍 (s + 1) (T₀'.append M) y₀) (restrict (lowerMask 𝔍 (s + 1) (T₀'.append M) y₀) T₁)
        ⟨p, hpW⟩ : Λ) : WithTop Λ) := by
  obtain ⟨h₁, hdom₁, hcan₁, hcos₁⟩ := hd₁
  rw [lowerValueL_eq_of_mem R 𝔍 _ h₁]
  congr 1
  set W' := lowerMask 𝔍 (s + 1) T₀' ((M.append T₁).proj p) with hW'
  set 𝔫 := geoTransformAlong (barMarked 𝔍) T₀' with h𝔫
  set E₀ := origMembers 𝔍 T₀' with hE₀
  -- the multiple test blow-ups
  have hT' : IsGeoTestTower (barMarked 𝔍) (T₀'.append (M.append T₁)) := by
    rw [← BlowupTower.append_assoc]; exact hT
  obtain ⟨hT₀', hMT⟩ := (isGeoTestTower_append_iff _ T₀' (M.append T₁)).mp hT'
  obtain ⟨hM', -⟩ := (isGeoTestTower_append_iff _ M T₁).mp hMT
  have hT₀ : IsGeoTestTower (barMarked 𝔍) (T₀'.append M) := ((isGeoTestTower_append_iff _ _ T₁).mp hT).1
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hwf : 𝔫.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T₀' hT₀'
  have hwf₀ : (geoTransformAlong (barMarked 𝔍) (T₀'.append M)).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ _ hT₀
  have hd𝔫 : 1 ≤ 𝔫.d := by
    rw [h𝔫, d_geoTransformAlong]; exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hE₀𝔫 : ∀ H ∈ E₀, H ∈ 𝔫.E := fun H hH => List.mem_of_mem_take hH
  -- (i) the restricted concatenation
  obtain ⟨hcanb, hval⟩ := inv_restrict_append R W' hdom₁ M T₁ hcan₁
  have hp₁ : (M.append T₁).proj p = M.proj (T₁.proj p) := by rw [BlowupTower.proj_append]; rfl
  have hq : p ∈ openPreimage T₁ (openPreimage M W') := show M.proj (T₁.proj p) ∈ W' from hp₁ ▸ h₁
  obtain ⟨hcosb, hvalb⟩ := hval p h₁ hq hcos₁
  rw [← hvalb]
  -- (ii) re-basing along `M`, whose centres miss `W'`
  have hS : membersThrough 𝔫.E E₀ (M.proj (T₁.proj p)) = membersThrough 𝔫.E E₀ ((M.append T₁).proj p) := by
    rw [hp₁]
  have e1 : lowerMarkedM 𝔍 (s + 1) T₀' ((M.append T₁).proj p) =
      MarkedIdeal.pullback (Subtype.val : W' → Y₁) (memberRestrict 𝔫 (membersThrough 𝔫.E E₀ (M.proj (T₁.proj p)))) := by
    rw [hS]; rfl
  rw [e1] at hdom₁ hcanb hcosb ⊢
  set q₀ : openPreimage M W' := ⟨T₁.proj p, hq⟩ with hq₀
  obtain ⟨hdomS, hcanS, -, hvalS⟩ := InvDomainRebase.memberRestrict_rebase hn R hwf hd𝔫 hE₀𝔫 M hM' W' hM q₀ hdom₁
    (restrict (openPreimage M W') T₁) hcanb
  rw [hvalS ⟨p, hq⟩ hcosb]
  -- (iii) the restricted marked ideal formed at `T₀` at the image of `p` is the one formed at `y₀`
  have hcongr : memberRestrict (geoTransformAlong 𝔫 M)
        (membersThrough (geoTransformAlong 𝔫 M).E (E₀.map (strictAlong M)) (q₀ : Y₀)) =
      memberRestrict (geoTransformAlong (barMarked 𝔍) (T₀'.append M))
        (membersThrough (geoTransformAlong (barMarked 𝔍) (T₀'.append M)).E (origMembers 𝔍 (T₀'.append M)) y₀) :=
    memberRestrict_membersThrough_congr (geoTransformAlong_append _ T₀' M).symm (origMembers_append 𝔍 T₀' M).symm
      (mem_origMembers_iff_of_mem_maskA 𝔍 (T₀'.append M) hpW hlp)
  rw [hcongr] at hdomS hcanS ⊢
  -- (iv) the values on the two open sets `W` and `M⁻¹W'`
  have hwfR := isWellFormed_memberRestrict hn hwf₀
    (membersThrough (geoTransformAlong (barMarked 𝔍) (T₀'.append M)).E (origMembers 𝔍 (T₀'.append M)) y₀)
  exact (inv_eq_of_two_opens R hwfR.isClosedSubmanifold_N hwfR.isCoherent T₁ hdom₀ hcan₀ hdomS hcanS hpW hq
    hcos₀).1.symm

end Succ

/-! ### Step 1bb: re-basing to the later stage (original members kept) -/

section Zero

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ} (R : ResolutionInvariant.{u, v} n k Λ)
  (𝔍 : MarkedIdeal n X)

/-- **Step 1b's restricted marked ideal with the divisor kept** on an open `W` of the stage `T₀`, for a function `w`:
`(𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩ V(w))_{T₀}})|_W`, `J̄ = 𝓒_N(𝓗_N(𝔍))` with the divisor of `𝔍`. -/
def contactKept (w : X → ℂ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (W : Opens Y₀) : MarkedIdeal n W :=
  MarkedIdeal.pullback (Subtype.val : W → Y₀)
    (withN (coeffMarkedAlong (geoTransformAlong (barMarked 𝔍) T₀)) (strictAlong T₀ (𝔍.N ∩ {x | w x = 0})))

/-- **The chosen tangent direction is one as soon as its open set contains the base point.** -/
theorem tangentChoice_spec_of_mem {x : X} (hx : x ∈ (tangentChoice 𝔍 x).1) :
    IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d (tangentChoice 𝔍 x).1 (tangentChoice 𝔍 x).2 := by
  classical
  by_cases h : ∃ (U : Set X) (w : X → ℂ), x ∈ U ∧ IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U w
  · exact (tangentChoice_spec 𝔍 h).2
  · rw [tangentChoice, dif_neg h] at hx
    exact absurd hx (notMem_empty x)

/-- **Step 1b's values re-based, divisor kept**: for a multiple test blow-up `T₀ T` of `J̄`, `u` a tangent direction on
`U`, `W ⊆ T₀⁻¹U` open with the centres of `T` missing `W`: if `contactKept 𝔍 u T₀ W` lies in the domain and `T|_W
T₁` is a canonical segment of it, then `contactKept 𝔍 u (T₀ T) (T⁻¹W)` lies in the domain, `T₁` is a canonical
segment of it, and the values agree on the cosupport (`restrictEquiv_restrictedCoeffHomAlong_rebase`, any divisor,
and `InvDomainRebase.inv_rebase`). -/
theorem contactKept_rebase (hN : IsClosedSubmanifold n 𝔍.N) (h𝔞 : 𝔍.ideal.IsCoherent) (hd : 1 ≤ 𝔍.d) (U : Opens X)
    {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T : BlowupTower Y₀ Y) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T)) (W : Opens Y₀)
    (hWU : (W : Set Y₀) ⊆ openPreimage T₀ U) (hW : CentresAvoid W T) (hdom : IsInvDomain k (contactKept 𝔍 u T₀ W))
    {Z : CMfd.{u} n} (T₁ : BlowupTower (CMfd.of (n := n) (openPreimage T W)) Z)
    (hcan : IsCanonical (contactKept 𝔍 u T₀ W) (R.inv (contactKept 𝔍 u T₀ W)) ((restrict W T).append T₁)) :
    IsInvDomain k (contactKept 𝔍 u (T₀.append T) (openPreimage T W)) ∧
      IsCanonical (contactKept 𝔍 u (T₀.append T) (openPreimage T W))
        (R.inv (contactKept 𝔍 u (T₀.append T) (openPreimage T W))) T₁ ∧
      ∀ z ∈ (geoTransformAlong (contactKept 𝔍 u T₀ W) ((restrict W T).append T₁)).cosupp,
        R.inv (contactKept 𝔍 u T₀ W) ((restrict W T).append T₁) z =
          R.inv (contactKept 𝔍 u (T₀.append T) (openPreimage T W)) T₁ z := by
  have he : IsEmptyTower (restrict W T) := (isEmptyTower_restrict_iff W T).mpr hW
  have hEq := ContactStageRebase.restrictEquiv_restrictedCoeffHomAlong_rebase 𝔍 hN h𝔞 hd U hu T₀ T hT W hWU hW
  have hJN : IsClosedSubmanifold n (barMarked 𝔍).N := hN
  have hJc := isCoherent_barMarked 𝔍 hN h𝔞
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc (T₀.append T) hT
  have hcoh : (contactKept 𝔍 u (T₀.append T) (openPreimage T W)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val (isCoherent_coeffMarkedAlong hcT hNT)
  exact InvDomainRebase.inv_rebase (X := CMfd.of (n := n) W) R hdom (restrict W T) he hEq hcoh T₁ hcan

/-- **The lower value of a point of level `0`, re-based to a later stage** (`hir:step-one-compare`, `s = 0`, masked
family): let `T₀' M T₁` be a multiple test blow-up of `J̄` (`𝔍` well formed, `d ≥ 1`) and `p` a point of the last
stage with lower data at level `0` at the split `T₀' (M T₁)`, such that the centres of `M` miss its mask `W'`. Then
`p` lies over `M⁻¹W'`, `contactKept 𝔍 v (T₀' M) (M⁻¹W')` (`v` the tangent direction chosen at the base point of `p`)
lies in the domain, `T₁|_{M⁻¹W'}` is a canonical segment of it, and the lower value of `p` is the value of `R` for
it at `p`. The change from `v` to the tangent direction of another point is `StepOneTangentChange`. -/
theorem lowerValue_eq_zero_rebase (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y₁ Y₀ Y : CMfd.{u} n}
    (T₀' : BlowupTower X Y₁) (M : BlowupTower Y₁ Y₀) (T₁ : BlowupTower Y₀ Y)
    (hT : IsGeoTestTower (barMarked 𝔍) ((T₀'.append M).append T₁)) {p : Y}
    (hd₁ : LowerDataL R 𝔍 (lowerMarkedM 𝔍) 0 T₀' (M.append T₁) p)
    (hM : CentresAvoid (lowerMask 𝔍 0 T₀' ((M.append T₁).proj p)) M) :
    ∃ hq : T₁.proj p ∈ openPreimage M (maskB 𝔍 T₀' ((M.append T₁).proj p)),
      IsInvDomain k (contactKept 𝔍 (tangentChoice 𝔍 (T₀'.proj ((M.append T₁).proj p))).2
        (T₀'.append M) (openPreimage M (maskB 𝔍 T₀' ((M.append T₁).proj p)))) ∧
      IsCanonical (contactKept 𝔍 (tangentChoice 𝔍 (T₀'.proj ((M.append T₁).proj p))).2
          (T₀'.append M) (openPreimage M (maskB 𝔍 T₀' ((M.append T₁).proj p))))
        (R.inv (contactKept 𝔍 (tangentChoice 𝔍 (T₀'.proj ((M.append T₁).proj p))).2
          (T₀'.append M) (openPreimage M (maskB 𝔍 T₀' ((M.append T₁).proj p)))))
        (restrict (openPreimage M (maskB 𝔍 T₀' ((M.append T₁).proj p))) T₁) ∧
      lowerValueL R 𝔍 (lowerMarkedM 𝔍) 0 T₀' (M.append T₁) p =
        ((R.inv (contactKept 𝔍 (tangentChoice 𝔍 (T₀'.proj ((M.append T₁).proj p))).2
          (T₀'.append M) (openPreimage M (maskB 𝔍 T₀' ((M.append T₁).proj p))))
          (restrict (openPreimage M (maskB 𝔍 T₀' ((M.append T₁).proj p))) T₁) ⟨p, hq⟩ : Λ) : WithTop Λ) := by
  obtain ⟨h₁, hdom₁, hcan₁, hcos₁⟩ := hd₁
  have hp₁ : (M.append T₁).proj p = M.proj (T₁.proj p) := by rw [BlowupTower.proj_append]; rfl
  have hq : T₁.proj p ∈ openPreimage M (maskB 𝔍 T₀' ((M.append T₁).proj p)) :=
    show M.proj (T₁.proj p) ∈ maskB 𝔍 T₀' ((M.append T₁).proj p) from hp₁ ▸ h₁
  refine ⟨hq, ?_⟩
  -- the tangent direction at the base point of `p`
  have hxU : T₀'.proj ((M.append T₁).proj p) ∈ (tangentChoice 𝔍 (T₀'.proj ((M.append T₁).proj p))).1 :=
    (interior_subset h₁).1
  have hU := tangentChoice_spec_of_mem 𝔍 hxU
  have hWU : ((maskB 𝔍 T₀' ((M.append T₁).proj p) : Opens Y₁) : Set Y₁) ⊆
      openPreimage T₀' ⟨(tangentChoice 𝔍 (T₀'.proj ((M.append T₁).proj p))).1, hU.isOpen⟩ :=
    fun z hz => (interior_subset hz).1
  have hT' : IsGeoTestTower (barMarked 𝔍) (T₀'.append M) := ((isGeoTestTower_append_iff _ _ T₁).mp hT).1
  -- (i) the restricted concatenation
  obtain ⟨hcanb, hval⟩ := inv_restrict_append R (maskB 𝔍 T₀' ((M.append T₁).proj p)) hdom₁ M T₁ hcan₁
  obtain ⟨hcosb, hvalb⟩ := hval p h₁ hq hcos₁
  -- (ii) re-basing along `M`
  obtain ⟨hdomS, hcanS, hvalS⟩ := contactKept_rebase R 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd
    ⟨(tangentChoice 𝔍 (T₀'.proj ((M.append T₁).proj p))).1, hU.isOpen⟩ hU T₀' M hT'
    (maskB 𝔍 T₀' ((M.append T₁).proj p)) hWU hM hdom₁ (restrict (openPreimage M (maskB 𝔍 T₀' ((M.append T₁).proj p))) T₁)
    hcanb
  refine ⟨hdomS, hcanS, ?_⟩
  rw [lowerValueL_eq_of_mem R 𝔍 _ h₁]
  congr 1
  exact hvalb.symm.trans (hvalS ⟨p, hq⟩ hcosb)

end Zero

/-! ### The cosupports of the lower marked ideals along restricted tails -/

section Cosupp

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **The cosupport of Step 1ab's lower marked ideal along the restricted tail** (`hir:step-one-compare`): along a
multiple test blow-up `T₀ T₁` of `J̄` (`𝔍` well formed, `0 < n`), for `y₀` in its own mask at level `s + 1` and
`T₁|_W` a multiple test blow-up of `𝓢(y₀)|_W`, a point over `W` lies in the cosupport of `𝓢(y₀)|_W` along `T₁|_W`
iff it lies in `cosupp J̄_{T₀ T₁}` and on the strict transforms of the original members through `y₀`
(`coeffAlong_restrict_withE_iff` on `W`, `strictAlong_inter_memberInter`). -/
theorem mem_cosupp_lowerMarked_succ_iff (h𝔍 : 𝔍.IsWellFormed) (hn : 0 < n) {s : ℕ}
    {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y)
    (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀} (hy₀ : y₀ ∈ lowerMask 𝔍 (s + 1) T₀ y₀)
    (hTW : IsGeoTestTower (lowerMarked 𝔍 (s + 1) T₀ y₀) (restrict (lowerMask 𝔍 (s + 1) T₀ y₀) T₁))
    (q : openPreimage T₁ (lowerMask 𝔍 (s + 1) T₀ y₀)) :
    q ∈ (geoTransformAlong (lowerMarked 𝔍 (s + 1) T₀ y₀) (restrict (lowerMask 𝔍 (s + 1) T₀ y₀) T₁)).cosupp ↔
      (q : Y) ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp ∧
        ∀ H ∈ origMembers 𝔍 T₀, y₀ ∈ H → (q : Y) ∈ strictAlong T₁ H := by
  classical
  set W := lowerMask 𝔍 (s + 1) T₀ y₀ with hWdef
  set 𝔫 := geoTransformAlong (barMarked 𝔍) T₀ with h𝔫
  set E₀ := origMembers 𝔍 T₀ with hE₀
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hwf : 𝔫.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T₀ hT₀
  have hd𝔫 : 1 ≤ 𝔫.d := by
    rw [h𝔫, d_geoTransformAlong]; exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hE₀𝔫 : ∀ H ∈ E₀, H ∈ 𝔫.E := fun H hH => List.mem_of_mem_take hH
  -- the restriction to `W` moved inside
  have h1 : lowerMarked 𝔍 (s + 1) T₀ y₀ = memberRestrict (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝔫)
      (membersThrough (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝔫).E (E₀.map ((Subtype.val : W → Y₀) ⁻¹' ·))
        (⟨y₀, hy₀⟩ : W)) :=
    InvDomainRebase.pullback_val_memberRestrict_membersThrough hwf hd𝔫 hE₀𝔫 W ⟨y₀, hy₀⟩
  set 𝔫W := MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝔫 with h𝔫W
  set S' := membersThrough 𝔫W.E (E₀.map ((Subtype.val : W → Y₀) ⁻¹' ·)) (⟨y₀, hy₀⟩ : W) with hS'
  have hwfW : 𝔫W.IsWellFormed := IsWellFormed.pullback_val hwf W
  have hwfS := isWellFormed_memberRestrict hn hwfW S'
  have hsub : ∀ H ∈ (memberRestrict 𝔫W S').E, H ∈ 𝔫W.E := by
    intro H hH
    rw [memberRestrict_E] at hH
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hH
    exact List.get_mem _ _
  have hA : ∀ H ∈ 𝔫W.E, H ∉ (memberRestrict 𝔫W S').E → 𝔫W.N ∩ memberInter 𝔫W.E S' ⊆ H := by
    intro H hH hHS x hx
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    by_cases hi : i ∈ S'
    · exact hx.2 i hi
    · exfalso
      apply hHS
      rw [memberRestrict_E]
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true hi⟩)
  have hiff := (CoefficientIdealAlongRestrictionDrop.coeffAlong_restrict_withE_iff 𝔫W hwfW hd𝔫
    hwfS.isClosedSubmanifold_N inter_subset_left hsub hA (restrict W T₁)).2
  have hTW' : IsGeoTestTower (memberRestrict 𝔫W S') (restrict W T₁) := h1 ▸ hTW
  have hcos : (geoTransformAlong (memberRestrict 𝔫W S') (restrict W T₁)).cosupp =
      (geoTransformAlong 𝔫W (restrict W T₁)).cosupp ∩
        strictAlong (restrict W T₁) (𝔫W.N ∩ memberInter 𝔫W.E S') := hiff hTW'
  -- the trace of the cosupport and of the strict transforms
  have hN1 : 𝔫W.N ∩ memberInter 𝔫W.E S' = (Subtype.val : W → Y₀) ⁻¹' (𝔫.N ∩ memberInter 𝔫.E
      (membersThrough 𝔫.E E₀ y₀)) := by
    have := congrArg MarkedIdeal.N h1
    exact this.symm
  rw [h1, hcos, hN1, strictAlong_restrict, ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hwf.isClosedSubmanifold_N hwf.isCoherent W T₁ hT₁, MemberInterTowerAlong.strictAlong_inter_memberInter 𝔫 hwf _ T₁ hT₁,
    geoTransformAlong_append]
  simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
  constructor
  · rintro ⟨hqc, -, hqS⟩
    refine ⟨hqc, fun H hH hyH => ?_⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (hE₀𝔫 H hH)
    exact hqS i (mem_membersThrough.mpr ⟨hH, hyH⟩)
  · rintro ⟨hqc, hqS⟩
    refine ⟨hqc, (geoTransformAlong 𝔫 T₁).cosupp_subset_N hqc, fun i hi => ?_⟩
    obtain ⟨hi₀, hyi⟩ := mem_membersThrough.mp hi
    exact hqS _ hi₀ hyi

open Classical in
/-- **Over a Step 1ab mask, the points of the level of `y₀` are those on the strict transforms of the original members through
`y₀`**: along `T₀ T₁` (closed members), a point `q` of the last stage over the mask of `y₀` has level `level y₀` iff it lies on
the strict transform along `T₁` of every original member through `y₀`. -/
theorem level_eq_iff_of_mem_maskA (hE : ∀ H ∈ 𝔍.E, IsClosed H) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Y) {y₀ : Y₀} {q : Y} (hq : T₁.proj q ∈ maskA 𝔍 T₀ y₀) :
    level 𝔍 (T₀.append T₁) q = level 𝔍 T₀ y₀ ↔ ∀ H ∈ origMembers 𝔍 T₀, y₀ ∈ H → q ∈ strictAlong T₁ H := by
  have himp : ∀ H ∈ origMembers 𝔍 T₀, T₁.proj q ∈ H → y₀ ∈ H := (interior_subset hq).1
  have hcl := isClosed_of_mem_origMembers 𝔍 hE T₀
  have hsub : (Finset.univ.filter fun i : Fin (origMembers 𝔍 T₀).length =>
        q ∈ strictAlong T₁ ((origMembers 𝔍 T₀).get i)) ⊆
      (Finset.univ.filter fun i : Fin (origMembers 𝔍 T₀).length => y₀ ∈ (origMembers 𝔍 T₀).get i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact himp _ (List.get_mem _ _)
      (MemberInterTowerAlong.strictAlong_subset_preimage T₁ (hcl _ (List.get_mem _ _)) hi)
  have hlev : level 𝔍 (T₀.append T₁) q = (Finset.univ.filter fun i : Fin (origMembers 𝔍 T₀).length =>
      q ∈ strictAlong T₁ ((origMembers 𝔍 T₀).get i)).card := by
    show boundaryCount (origMembers 𝔍 (T₀.append T₁)) q = _
    rw [origMembers_append, boundaryCount_map]
  have hlev₀ : level 𝔍 T₀ y₀ = (Finset.univ.filter fun i : Fin (origMembers 𝔍 T₀).length =>
      y₀ ∈ (origMembers 𝔍 T₀).get i).card := rfl
  rw [hlev, hlev₀]
  constructor
  · intro hc H hH hyH
    have heq := Finset.eq_of_subset_of_card_le hsub hc.ge
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    have hi : i ∈ (Finset.univ.filter fun i : Fin (origMembers 𝔍 T₀).length => y₀ ∈ (origMembers 𝔍 T₀).get i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hyH
    rw [← heq] at hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro hall
    refine le_antisymm (Finset.card_le_card hsub) (Finset.card_le_card fun i hi => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hall _ (List.get_mem _ _) hi

/-- **Step 1bb's restricted tails, divisor kept** (`hir:step-one-compare`): along a multiple test blow-up `T₀ T₁` of
`J̄` (`𝔍` well formed, `d ≥ 1`, of maximal order), for `y₀` in the cosupport at `T₀`, `T₁|_W` is a multiple test
blow-up of the masked lower marked ideal of level `0` and its cosupport is the trace of `cosupp J̄_{T₀ T₁}`
(`ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le`, any divisor). -/
theorem isGeoTestTower_cosupp_lowerMarkedB (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y)
    (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀}
    (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) :
    IsGeoTestTower (lowerMarkedB 𝔍 T₀ y₀) (restrict (maskB 𝔍 T₀ y₀) T₁) ∧
      (geoTransformAlong (lowerMarkedB 𝔍 T₀ y₀) (restrict (maskB 𝔍 T₀ y₀) T₁)).cosupp =
        (Subtype.val : openPreimage T₁ (maskB 𝔍 T₀ y₀) → Y) ⁻¹'
          (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp := by
  obtain ⟨hT₀, -⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  obtain ⟨hxU, hU⟩ := tangentChoice_spec 𝔍 (exists_tangent_of_mem_cosupp 𝔍 h𝔍 hd hmax T₀ hT₀ hy₀)
  have hWU : ((maskB 𝔍 T₀ y₀ : Opens Y₀) : Set Y₀) ⊆
      openPreimage T₀ ⟨(tangentChoice 𝔍 (T₀.proj y₀)).1, hU.isOpen⟩ := fun z hz => (interior_subset hz).1
  exact ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd
    ⟨(tangentChoice 𝔍 (T₀.proj y₀)).1, hU.isOpen⟩ hU T₀ T₁ hT (maskB 𝔍 T₀ y₀) hWU

end Cosupp

end

end Hironaka.StepOneCompare
