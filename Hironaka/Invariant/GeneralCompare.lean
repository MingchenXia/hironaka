/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.GeneralValue
import Hironaka.Invariant.StepOneCompare
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionOpen
import Hironaka.Invariant.CompanionRebase
import Hironaka.Invariant.CompanionReductionAlong
import Hironaka.Invariant.ContactCanonicalAlong
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Invariant.InvDomainCompanion
import Hironaka.Invariant.InvDomainRebase
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.MaxOrderValue
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.NonmonomialOrderTail
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Invariant.StepOneEmptyPrefix
import Hironaka.Invariant.StepOneNearby
import Hironaka.Invariant.StepOneRestrictOpen
import Hironaka.Invariant.StepOneTowerIso
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The general value of a nearby point through the reference point's companion ideal

Sources: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 2a (the companion ideal formed
where the order was reached, computed along the part of the resolution after it) and the lemma on the commutativity
of the resolution procedure with étale morphisms (re-basing across steps which are isomorphisms near the point).

Let `T = T₀' M T₁` be a multiple test blow-up of `𝔪` (in the domain, `0 < n`), `o ≥ 1`, and `p` a point of the last
stage whose run in the regime of order `o` started at `T₀'` (lower data there, `GeneralValue.GenLowerData`), while a
reference point started at `T₀ = T₀' M`. If the centres of `M` miss the mask `W' = {ν ≤ o}` of `T₀'` (they lie in
`{ν ≥ o + 1}`: `NonmonomialOrderCanonical.centresAvoid_of_canonical`), the companion value of `p` is the value of
the maximal-order value function `M` for the companion ideal formed at `T₀` on its mask `W`, along `T₁|_W`
(`genLowerValue_eq_rebase`):

1. `(M T₁)|_{W'}` is isomorphic to `M|_{W'}` followed by `T₁|_{M⁻¹W'}` (`value_restrict_append`;
   `isTowerIso_restrict_append`);
2. `M|_{W'}` has only empty centres, and the companion ideal of `𝔪_{T₀'}` on `W'`, transformed along it, is
   restricted-equivalent to the companion ideal of `𝔪_{T₀}` on `M⁻¹W'`
   (`CompanionRebase.restrictEquiv_companionOf_rebase`), so the values re-base
   (`MaxOrderValue.IsMaxOrderValue.value_rebase`);
3. the companion ideals of `𝔪_{T₀}` on the two open sets `M⁻¹W'` and `W` are restrictions of one marked ideal, and the values
   on two open sets agree (`value_eq_of_two_opens`, from `value_restrict_nestedOpens`).

These are the maximal-order-value versions of `MaxLocusLocal.restrict_nestedOpens`, `StepOneNearby.inv_eq_of_two_opens` and
`StepOneCompare.inv_restrict_append` (stated there for resolution invariants), and the analogue of
`StepOneCompare.lowerValue_eq_succ` for the general step.

## Main results

* `value_restrict_nestedOpens`, **`value_eq_of_two_opens`**, **`value_restrict_append`**: tools for a maximal-order value;
* `compAt_eq_pullback`, `isInvDomain_compAt`, `isMaximalOrderAlong_compAt`: the companion ideal formed at a stage lies in the
  domain and is of maximal order;
* **`genLowerValue_eq_rebase`**: the companion value of a point which started earlier, through the later companion ideal.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralCompare

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.CompanionReductionAlong Hironaka.CompanionRebase Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdealRestrictOpen Hironaka.BlowupTowerIsomorphism Hironaka.RestrictEmptyTower Hironaka.StepOneRegime Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderRegime Hironaka.NonmonomialOrderCanonical Hironaka.NonmonomialOrderTail Hironaka.HomogenizedIdealAlong Hironaka.MaxOrderValue Hironaka.GeneralValue Hironaka.MaxLocusLocal Hironaka.InvDomainCompanion Hironaka.CompanionOpen
open Hironaka.BlowupTowerIsoTail (opensCongr isTowerIso_restrict_append openPreimage_append)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (IsEmptyTower)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

/-! ### Tools for a maximal-order value -/

section Tools

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ}
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Nested open sets** (`MaxLocusLocal.restrict_nestedOpens` for a maximal-order value): for `V ⊆ W` open, if `𝔫|_W` lies in
the domain, is of maximal order and `T|_W` is a canonical segment of it, then so for `𝔫|_V` and `T|_V`, and the values agree at
the points of the cosupport over `V`. -/
theorem value_restrict_nestedOpens (hM : IsMaxOrderValue n k M) {𝔫 : MarkedIdeal n X} (h𝔫 : 𝔫.ideal.IsCoherent)
    {W V : Opens X} (hVW : V ≤ W) (hdom : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫))
    (hmax : IsMaximalOrderAlong (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫).N
      (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫).ideal (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫).d)
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫)
      (M (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫)) (restrict W T)) :
    IsInvDomain k (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫) ∧
      IsMaximalOrderAlong (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫).N
        (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫).ideal (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫).d ∧
      IsCanonical (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫)
        (M (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫)) (restrict V T) ∧
      ∀ p : openPreimage T V,
        p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫) (restrict V T)).cosupp →
        M (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫) (restrict V T) p =
          M (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫) (restrict W T) ⟨(p : Y), openPreimage_mono T hVW p.2⟩ := by
  have hdom' := InvDomainTowerAlong.isInvDomain_pullback_val (nestedOpens W V) hdom
  obtain ⟨-, -, hmax', -⟩ := StepOneRestrictOpen.hypotheses_restrict (X := CMfd.of (n := n) W)
    (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫) (nestedOpens W V) hdom.isWellFormed hdom.one_le_d hmax hdom.dimLE
  have hcan' := hM.isCanonical_restrict hdom hmax (nestedOpens W V) (restrict W T) hcan
  have hiso := (isTowerIso_restrict_nestedOpens (X := X) hVW T).symm
  have heq := pullback_symm_nestedOpensDiffeo (M := X) h𝔫 hVW
  have hdomV := InvDomainTowerAlong.isInvDomain_pullback (nestedOpensDiffeo (n := n) hVW).symm hdom'
  obtain ⟨-, -, hmaxV, -⟩ := StepOneTowerIso.hypotheses_pullback (nestedOpensDiffeo (n := n) hVW).symm _
    hdom'.isWellFormed hdom'.one_le_d hmax' hdom'.dimLE
  rw [heq] at hdomV hmaxV
  have hcanV := hM.isCanonical_of_isTowerIso hdom' hmax' (nestedOpensDiffeo (n := n) hVW).symm hiso hcan'
  rw [heq] at hcanV
  refine ⟨hdomV, hmaxV, hcanV, fun p hp => ?_⟩
  have hTt' := hM.isGeoTestTower_of_isCanonical hdom' hmax' _ hcan'
  have hcos := IsTowerIso.cosupp_geoTransformAlong (nestedOpensDiffeo (n := n) hVW).symm
    hdom'.isWellFormed.isClosedSubmanifold_N hdom'.isWellFormed.isCoherent hiso hTt'
  rw [heq] at hcos
  have hp' := hp
  rw [hcos] at hp'
  have key := hM.towerIso (nestedOpensDiffeo (n := n) hVW).symm _ hdom' hmax' _ _ _ hiso hcan' p hp'
  rw [heq] at key
  rw [key]
  have hTt := hM.isGeoTestTower_of_isCanonical hdom hmax _ hcan
  have hp'' := hp'
  rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent (nestedOpens W V) (restrict W T) hTt] at hp''
  exact hM.restrictOpen _ hdom hmax (nestedOpens W V) (restrict W T) hcan
    ((nestedDiffeo (openPreimage T W) (openPreimage (restrict W T) (nestedOpens W V)) (openPreimage T V)
      (mem_openPreimage_restrict_nestedOpens W V T) (openPreimage_mono T hVW)).symm p) hp''

/-- **Values on two open sets** (`StepOneNearby.inv_eq_of_two_opens` for a maximal-order value): let `𝔫` have a coherent ideal
and `N` a closed submanifold, and `A`, `B` opens of the base of `T` such that `𝔫|_A`, `𝔫|_B` lie in the domain, are of maximal
order and `T|_A`, `T|_B` are canonical segments of them.  At a point over `A ∩ B` in the cosupport along `T|_A` the two values
agree, and the point lies in the cosupport along `T|_B`. -/
theorem value_eq_of_two_opens (hM : IsMaxOrderValue n k M) {𝔫 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔫.N)
    (h𝔫 : 𝔫.ideal.IsCoherent) {A B : Opens X} {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hA : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : A → X) 𝔫))
    (hmaxA : IsMaximalOrderAlong (MarkedIdeal.pullback (Subtype.val : A → X) 𝔫).N
      (MarkedIdeal.pullback (Subtype.val : A → X) 𝔫).ideal (MarkedIdeal.pullback (Subtype.val : A → X) 𝔫).d)
    (hcanA : IsCanonical (MarkedIdeal.pullback (Subtype.val : A → X) 𝔫)
      (M (MarkedIdeal.pullback (Subtype.val : A → X) 𝔫)) (restrict A T))
    (hB : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : B → X) 𝔫))
    (hmaxB : IsMaximalOrderAlong (MarkedIdeal.pullback (Subtype.val : B → X) 𝔫).N
      (MarkedIdeal.pullback (Subtype.val : B → X) 𝔫).ideal (MarkedIdeal.pullback (Subtype.val : B → X) 𝔫).d)
    (hcanB : IsCanonical (MarkedIdeal.pullback (Subtype.val : B → X) 𝔫)
      (M (MarkedIdeal.pullback (Subtype.val : B → X) 𝔫)) (restrict B T))
    {p : Y} (hpA : T.proj p ∈ A) (hpB : T.proj p ∈ B)
    (hcos : (⟨p, hpA⟩ : openPreimage T A) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : A → X) 𝔫) (restrict A T)).cosupp) :
    M (MarkedIdeal.pullback (Subtype.val : A → X) 𝔫) (restrict A T) ⟨p, hpA⟩ =
        M (MarkedIdeal.pullback (Subtype.val : B → X) 𝔫) (restrict B T) ⟨p, hpB⟩ ∧
      (⟨p, hpB⟩ : openPreimage T B) ∈
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : B → X) 𝔫) (restrict B T)).cosupp := by
  have hVA : A ⊓ B ≤ A := inf_le_left
  have hVB : A ⊓ B ≤ B := inf_le_right
  obtain ⟨-, -, -, hvalA⟩ := value_restrict_nestedOpens hM h𝔫 hVA hA hmaxA T hcanA
  obtain ⟨-, -, -, hvalB⟩ := value_restrict_nestedOpens hM h𝔫 hVB hB hmaxB T hcanB
  have hTA := hM.isGeoTestTower_of_isCanonical hA hmaxA _ hcanA
  have hTB := hM.isGeoTestTower_of_isCanonical hB hmaxB _ hcanB
  let q : openPreimage T (A ⊓ B) := ⟨p, show T.proj p ∈ (A : Set X) ∩ B from ⟨hpA, hpB⟩⟩
  have hqV := (StepOneNearby.mem_cosupp_restrict_nested_iff hN h𝔫 hVA T hTA q).mpr hcos
  exact ⟨(hvalA q hqV).symm.trans (hvalB q hqV),
    (StepOneNearby.mem_cosupp_restrict_nested_iff hN h𝔫 hVB T hTB q).mp hqV⟩

/-- **Canonical segments and values along a restricted concatenation** (`StepOneCompare.inv_restrict_append` for a
maximal-order value): if `(M T₁)|_W` is a canonical segment of `𝔪` (on `W`, in the domain, of maximal order), so is `M|_W`
followed by `T₁|_{M⁻¹W}`, and at the points of the cosupport the values agree. -/
theorem value_restrict_append (hM : IsMaxOrderValue n k M) {Y₁ Y₀ Y : CMfd.{u} n} (W : Opens Y₁)
    {𝔪 : MarkedIdeal n (CMfd.of (n := n) W)} (hdom : IsInvDomain k 𝔪) (hmax : IsMaximalOrderAlong 𝔪.N 𝔪.ideal 𝔪.d)
    (Mt : BlowupTower Y₁ Y₀) (T₁ : BlowupTower Y₀ Y) (hcan : IsCanonical 𝔪 (M 𝔪) (restrict W (Mt.append T₁))) :
    IsCanonical 𝔪 (M 𝔪) ((restrict W Mt).append (restrict (openPreimage Mt W) T₁)) ∧
      ∀ (p : Y) (h : p ∈ openPreimage (Mt.append T₁) W) (h' : p ∈ openPreimage T₁ (openPreimage Mt W)),
        (⟨p, h⟩ : openPreimage (Mt.append T₁) W) ∈ (geoTransformAlong 𝔪 (restrict W (Mt.append T₁))).cosupp →
        (⟨p, h'⟩ : openPreimage T₁ (openPreimage Mt W)) ∈
            (geoTransformAlong 𝔪 ((restrict W Mt).append (restrict (openPreimage Mt W) T₁))).cosupp ∧
          M 𝔪 ((restrict W Mt).append (restrict (openPreimage Mt W) T₁)) ⟨p, h'⟩ =
            M 𝔪 (restrict W (Mt.append T₁)) ⟨p, h⟩ := by
  have hiso := (isTowerIso_restrict_append W Mt T₁).symm
  have hpb : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) W) ∞).symm 𝔪 = 𝔪 :=
    ContactCanonicalAlong.pullback_id 𝔪 hdom.isWellFormed.isCoherent
  have hcan' := hM.isCanonical_of_isTowerIso hdom hmax _ hiso hcan
  rw [hpb] at hcan'
  refine ⟨hcan', fun p h h' hp => ?_⟩
  have hTt := hM.isGeoTestTower_of_isCanonical hdom hmax _ hcan
  have hcos := IsTowerIso.cosupp_geoTransformAlong _ hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent hiso hTt
  rw [hpb] at hcos
  have hχ : (opensCongr (n := n) (openPreimage_append Mt T₁ W).symm).symm ⟨p, h'⟩ = ⟨p, h⟩ := Subtype.ext rfl
  have hp' : (⟨p, h'⟩ : openPreimage T₁ (openPreimage Mt W)) ∈
      (geoTransformAlong 𝔪 ((restrict W Mt).append (restrict (openPreimage Mt W) T₁))).cosupp := by
    rw [hcos, mem_preimage, hχ]
    exact hp
  refine ⟨hp', ?_⟩
  have key := hM.towerIso _ 𝔪 hdom hmax _ _ _ hiso hcan ⟨p, h'⟩ (by rw [hχ]; exact hp)
  rw [hpb, hχ] at key
  exact key

end Tools

/-! ### The companion ideal formed at a stage -/

section Companion

variable {X : CMfd.{u} n} {k : ℕ}

/-- The companion ideal formed at `T₀` on its mask is the restriction of the companion ideal of `𝔪_{T₀}`. -/
theorem compAt_eq_pullback (hn : 0 < n) {𝔪 : MarkedIdeal n X} (o : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (h : IsInvDomain k (geoTransformAlong 𝔪 T₀)) :
    compAt 𝔪 o T₀ = MarkedIdeal.pullback (Subtype.val : ordMask (geoTransformAlong 𝔪 T₀) o → Y₀)
      (companionOf n (geoTransformAlong 𝔪 T₀) o) :=
  (pullback_val_companionOf hn h.isWellFormed h.isNonzeroAlongAt _ o).symm

/-- **The companion ideal formed at a stage lies in the domain** (`o ≥ 1`). -/
theorem isInvDomain_compAt (hn : 0 < n) {𝔪 : MarkedIdeal n X} {o : ℕ} (ho : 1 ≤ o) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (h : IsInvDomain k (geoTransformAlong 𝔪 T₀)) : IsInvDomain k (compAt 𝔪 o T₀) :=
  isInvDomain_companionAlong_pullback_val hn h _ ho

/-- **The companion ideal formed at a stage is of maximal order** (on the mask `{ν ≤ o}`). -/
theorem isMaximalOrderAlong_compAt (hn : 0 < n) {𝔪 : MarkedIdeal n X} (o : ℕ) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (h : IsInvDomain k (geoTransformAlong 𝔪 T₀)) :
    IsMaximalOrderAlong (compAt 𝔪 o T₀).N (compAt 𝔪 o T₀).ideal (compAt 𝔪 o T₀).d := by
  have hmax := isMaximalOrderAlong_companionOf_pullback_val hn h (ordMask (geoTransformAlong 𝔪 T₀) o)
    fun x _ hxW => (mem_ordMask_iff hn h.isWellFormed h.isNonzeroAlongAt o x).mp hxW
  have hN : (compAt 𝔪 o T₀).N =
      (MarkedIdeal.pullback (Subtype.val : ordMask (geoTransformAlong 𝔪 T₀) o → Y₀) (geoTransformAlong 𝔪 T₀)).N :=
    companionAlong_N _ _ _ _ _ _
  rw [hN]
  exact hmax

end Companion

/-! ### The comparison -/

section Compare

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ}
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The companion value of a point which started earlier, through the later companion ideal**
(`hir:general-compare`): let `T₀' Mt T₁` be such that `T₀' Mt` is a multiple test blow-up of `𝔪` (in the domain, `0 < n`),
`o ≥ 1`, the centres of `Mt` miss the mask `W'` of `T₀'`, and `p` a point of the last stage with lower data at the split
`T₀' (Mt T₁)`.  If the image of `p` at `T₀ = T₀' Mt` lies in the mask `W` of `T₀` and `T₁|_W` is a canonical segment of the
companion ideal formed at `T₀`, then the companion value of `p` is the value of `M` for that companion ideal along `T₁|_W`, and
`p` lies in its cosupport. -/
theorem genLowerValue_eq_rebase (hM : IsMaxOrderValue n k M) (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    {o : ℕ} (ho : 1 ≤ o) {Y₁ Y₀ Y : CMfd.{u} n} (T₀' : BlowupTower X Y₁) (Mt : BlowupTower Y₁ Y₀)
    (T₁ : BlowupTower Y₀ Y) (hT : IsGeoTestTower 𝔪 (T₀'.append Mt))
    (hMt : CentresAvoid (ordMask (geoTransformAlong 𝔪 T₀') o) Mt) {p : Y}
    (hd : GenLowerData M k 𝔪 o T₀' (Mt.append T₁) p)
    (hpW : T₁.proj p ∈ ordMask (geoTransformAlong 𝔪 (T₀'.append Mt)) o)
    (hcan₀ : IsCanonical (compAt 𝔪 o (T₀'.append Mt)) (M (compAt 𝔪 o (T₀'.append Mt)))
      (restrict (ordMask (geoTransformAlong 𝔪 (T₀'.append Mt)) o) T₁)) :
    genLowerValue M 𝔪 o T₀' (Mt.append T₁) p =
        ((M (compAt 𝔪 o (T₀'.append Mt)) (restrict (ordMask (geoTransformAlong 𝔪 (T₀'.append Mt)) o) T₁)
          ⟨p, hpW⟩ : Λ) : WithTop Λ) ∧
      (⟨p, hpW⟩ : openPreimage T₁ (ordMask (geoTransformAlong 𝔪 (T₀'.append Mt)) o)) ∈
        (geoTransformAlong (compAt 𝔪 o (T₀'.append Mt))
          (restrict (ordMask (geoTransformAlong 𝔪 (T₀'.append Mt)) o) T₁)).cosupp := by
  obtain ⟨h₁, hdom₁, hmax₁, hcan₁, hcos₁⟩ := hd
  obtain ⟨hT₀', hMt'⟩ := (isGeoTestTower_append_iff 𝔪 T₀' Mt).mp hT
  have hdom₀' := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀' hT₀'
  have hdom₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (T₀'.append Mt) hT
  -- (i) the restricted concatenation
  obtain ⟨hcanb, hval⟩ := value_restrict_append hM (ordMask (geoTransformAlong 𝔪 T₀') o) hdom₁ hmax₁ Mt T₁ hcan₁
  have hp₁ : (Mt.append T₁).proj p = Mt.proj (T₁.proj p) := by rw [BlowupTower.proj_append]; rfl
  have hq : p ∈ openPreimage T₁ (openPreimage Mt (ordMask (geoTransformAlong 𝔪 T₀') o)) :=
    show Mt.proj (T₁.proj p) ∈ ordMask (geoTransformAlong 𝔪 T₀') o from hp₁ ▸ h₁
  obtain ⟨hcosb, hvalb⟩ := hval p h₁ hq hcos₁
  rw [genLowerValue_eq_of_mem M 𝔪 h₁, ← hvalb]
  -- (ii) the companion ideal re-based along `Mt`, whose centres miss the earlier mask
  have he : IsEmptyTower (restrict (ordMask (geoTransformAlong 𝔪 T₀') o) Mt) :=
    (isEmptyTower_restrict_iff _ Mt).mpr hMt
  have hEq := restrictEquiv_companionOf_rebase hn hdom₀' ho Mt hMt' (ordMask (geoTransformAlong 𝔪 T₀') o) hMt
  rw [pullback_val_companionOf hn hdom₀'.isWellFormed hdom₀'.isNonzeroAlongAt _ o,
    ← geoTransformAlong_append] at hEq
  have hdomA := isInvDomain_pullback_val_companionAlong hn hdom₀
    (openPreimage Mt (ordMask (geoTransformAlong 𝔪 T₀') o)) ho
  have hmaxA : IsMaximalOrderAlong
      (MarkedIdeal.pullback (Subtype.val : openPreimage Mt (ordMask (geoTransformAlong 𝔪 T₀') o) → Y₀)
        (companionOf n (geoTransformAlong 𝔪 (T₀'.append Mt)) o)).N
      (MarkedIdeal.pullback (Subtype.val : openPreimage Mt (ordMask (geoTransformAlong 𝔪 T₀') o) → Y₀)
        (companionOf n (geoTransformAlong 𝔪 (T₀'.append Mt)) o)).ideal
      (MarkedIdeal.pullback (Subtype.val : openPreimage Mt (ordMask (geoTransformAlong 𝔪 T₀') o) → Y₀)
        (companionOf n (geoTransformAlong 𝔪 (T₀'.append Mt)) o)).d := by
    rw [pullback_val_companionOf hn hdom₀.isWellFormed hdom₀.isNonzeroAlongAt _ o]
    have hN : (companionOf n (M := CMfd.of (n := n) (openPreimage Mt (ordMask (geoTransformAlong 𝔪 T₀') o)))
        (MarkedIdeal.pullback (Subtype.val : openPreimage Mt (ordMask (geoTransformAlong 𝔪 T₀') o) → Y₀)
          (geoTransformAlong 𝔪 (T₀'.append Mt))) o).N =
        (MarkedIdeal.pullback (Subtype.val : openPreimage Mt (ordMask (geoTransformAlong 𝔪 T₀') o) → Y₀)
          (geoTransformAlong 𝔪 (T₀'.append Mt))).N :=
      companionAlong_N _ _ _ _ _ _
    rw [hN]
    refine isMaximalOrderAlong_companionOf_pullback_val hn hdom₀ _ fun x _ hxA hx1 => ?_
    have hiff := mem_ordGe_geoTransformAlong_of_centresAvoid hn hdom₀' Mt hMt' _ hMt (o + 1) hxA
    rw [← geoTransformAlong_append] at hiff
    exact (mem_ordMask_iff hn hdom₀'.isWellFormed hdom₀'.isNonzeroAlongAt o _).mp hxA (hiff.mp hx1)
  have hmax₀ := (StepOneEmptyPrefix.hypotheses_emptyPrefix (compAt 𝔪 o T₀') hdom₁.isWellFormed hdom₁.one_le_d hmax₁
    hdom₁.dimLE _ he).2.2.1
  obtain ⟨-, hcanA, hvalA⟩ := hM.value_rebase hdom₁ hmax₁ _ he hEq hdomA.isWellFormed.isCoherent hmaxA hmax₀
    (restrict (openPreimage Mt (ordMask (geoTransformAlong 𝔪 T₀') o)) T₁) hcanb
  rw [hvalA _ hcosb]
  have hcosA : (⟨p, hq⟩ : openPreimage T₁ (openPreimage Mt (ordMask (geoTransformAlong 𝔪 T₀') o))) ∈
      (geoTransformAlong (MarkedIdeal.pullback
        (Subtype.val : openPreimage Mt (ordMask (geoTransformAlong 𝔪 T₀') o) → Y₀)
        (companionOf n (geoTransformAlong 𝔪 (T₀'.append Mt)) o))
        (restrict (openPreimage Mt (ordMask (geoTransformAlong 𝔪 T₀') o)) T₁)).cosupp := by
    have hc := (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong hEq
      hdomA.isWellFormed.isClosedSubmanifold_N.1 hdomA.isWellFormed.isCoherent
      (InvDomainRebase.isInvDomain_geoTransformAlong_of_isEmptyTower hdom₁ _ he).isWellFormed.isCoherent
      (restrict (openPreimage Mt (ordMask (geoTransformAlong 𝔪 T₀') o)) T₁)).1
    rw [hc, ← geoTransformAlong_append]
    exact hcosb
  -- (iii) the two open sets `Mt⁻¹ W'` and `W` of the stage `T₀`
  have hdomC := isInvDomain_companionAlong_geoTransformAlong hn h (T₀'.append Mt) hT ho
  rw [compAt_eq_pullback hn o (T₀'.append Mt) hdom₀] at hcan₀ ⊢
  have hdomB := isInvDomain_pullback_val_companionAlong hn hdom₀ (ordMask (geoTransformAlong 𝔪 (T₀'.append Mt)) o) ho
  have hmaxB := isMaximalOrderAlong_compAt hn o (T₀'.append Mt) hdom₀
  rw [compAt_eq_pullback hn o (T₀'.append Mt) hdom₀] at hmaxB
  obtain ⟨hv, hc⟩ := value_eq_of_two_opens hM hdomC.isWellFormed.isClosedSubmanifold_N hdomC.isWellFormed.isCoherent T₁
    hdomA hmaxA hcanA hdomB hmaxB hcan₀ hq hpW hcosA
  exact ⟨congrArg _ hv, hc⟩

end Compare

end

end Hironaka.GeneralCompare
