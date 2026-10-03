/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.GeneralRestrictOpen
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionOpen
import Hironaka.Invariant.CompanionRebase
import Hironaka.Invariant.CompanionReductionAlong
import Hironaka.Invariant.ContactLowerValue
import Hironaka.Invariant.GeneralAdmissible
import Hironaka.Invariant.GeneralCanonicalTail
import Hironaka.Invariant.GeneralCompare
import Hironaka.Invariant.GeneralRepresentative
import Hironaka.Invariant.GeneralValue
import Hironaka.Invariant.GeneralValueOrderZero
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Invariant.InvDomainCompanion
import Hironaka.Invariant.InvDomainRebase
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxOrderValue
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Invariant.NonmonomialOrderTail
import Hironaka.Invariant.NonmonomialOrderTransport
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Invariant.StepOneEmptyPrefix
import Hironaka.Invariant.StepOneRegime
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Re-basing the general value after an empty prefix: property (4')

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`: extensions of the resolution insert
isomorphisms, and the invariants of points transformed isomorphically do not change; Bierstone--Milman 2008, Step
II.

Let `𝔪` be a marked ideal of the domain (`0 < n`), `P` a tower with only empty centres and `P T₁` a canonical
segment of the general value `genInv M 𝔪`. At a point `z` of the cosupport of positive order `o`, the general value
of `𝔪` along `P T₁` is that of `𝔪_P` along `T₁`. The orders agree (`geoTransformAlong_append`) and the regimes along
`P H` and along `H` correspond (`NonmonomialOrderTransport.ordRegime_append_iff`).

* If the run of `z` along `T₁` is shorter than `T₁`, both runs agree and the split of `P T₁` at it is `P` followed by the split of
  `T₁` (`StepOneEmptyPrefix.regimeRun_append_of_lt`, `split_append_of_le`): the companion values are computed from the same
  transform (`GeneralRepresentative.genLowerValue_congr_of_eq`).
* If the run covers `T₁`, it covers `P` too (`regimeRun_ordRegime_isEmptyTower`): along `P T₁` the companion ideal
  is formed at the base, along `T₁` for `𝔪_P` at the base of `T₁`. They are related by re-basing across the empty
  restricted tower `P|_W` (`genLowerValue_refl_append_of_isEmptyTower`: `GeneralCompare.value_restrict_append`,
  `CompanionRebase.restrictEquiv_companionOf_rebase`, property (4') of `M` through
  `MaxOrderValue.IsMaxOrderValue.value_rebase`), and the mask of `𝔪_P` is the preimage of that of `𝔪`
  (`NonmonomialOrderTransport.ordMask_isEmptyTower`).

At order `0` this is `GeneralValueOrderZero.emptyPrefix_field_of_nmOrd_eq_zero`.

## Main results

* `genLowerValue_refl_append_of_isEmptyTower`: the companion value formed at the base, across an empty prefix;
* **`genInv_emptyPrefix_of_pos`**: property (4') of the general value at positive order;
* **`emptyPrefix_field`**: property (4') in the shape of the field `emptyPrefix` of `ResolutionInvariantExt.ResolutionInvariant`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralEmptyPrefix

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.CompanionReductionAlong Hironaka.CompanionRebase Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdealRestrictOpen Hironaka.RestrictEmptyTower Hironaka.StepOneRegime Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderRegime Hironaka.NonmonomialOrderTail Hironaka.NonmonomialOrderTransport Hironaka.InvDomainCompanion Hironaka.MaxOrderValue Hironaka.GeneralValue Hironaka.GeneralCompare Hironaka.GeneralCanonicalTail Hironaka.HomogenizedIdealAlong Hironaka.StepOneEmptyPrefix Hironaka.CompanionOpen
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-! ### The companion value formed at the base, across an empty prefix -/

/-- **Re-basing the companion value across an empty prefix**: for `𝔪` in the domain (`0 < n`, `o ≥ 1`), `P` a tower with only
empty centres and `z` a point of the last stage of `P T₁` with lower data at the split `refl (P T₁)` (the companion ideal formed at
the base), the companion value of `z` at that split is its companion value at the split `P T₁`. -/
theorem genLowerValue_refl_append_of_isEmptyTower (hM : IsMaxOrderValue n k M) (hn : 0 < n) {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) {o : ℕ} (ho : 1 ≤ o) {Y₁ Y : CMfd.{u} n} (P : BlowupTower X Y₁) (hP : IsEmptyTower P)
    (T₁ : BlowupTower Y₁ Y) {z : Y} (hd : GenLowerData M k 𝔪 o .refl (P.append T₁) z) :
    genLowerValue M 𝔪 o .refl (P.append T₁) z = genLowerValue M 𝔪 o P T₁ z := by
  obtain ⟨h₁, hdom₁, hmax₁, hcan₁, hcos₁⟩ := hd
  have hPt : IsGeoTestTower 𝔪 P := isGeoTestTower_of_isEmptyTower 𝔪 P hP
  have hdomP := InvDomainRebase.isInvDomain_geoTransformAlong_of_isEmptyTower h P hP
  have hMt : CentresAvoid (ordMask 𝔪 o) P := ContactLowerValue.centresAvoid_of_isEmptyTower (ordMask 𝔪 o) P hP
  -- (i) the restricted concatenation
  obtain ⟨hcanb, hval⟩ := value_restrict_append hM (ordMask (geoTransformAlong 𝔪 .refl) o) hdom₁ hmax₁ P T₁ hcan₁
  have hp₁ : (P.append T₁).proj z = P.proj (T₁.proj z) := by rw [BlowupTower.proj_append]; rfl
  have hq : z ∈ openPreimage T₁ (openPreimage P (ordMask (geoTransformAlong 𝔪 .refl) o)) :=
    show P.proj (T₁.proj z) ∈ ordMask (geoTransformAlong 𝔪 .refl) o from hp₁ ▸ h₁
  obtain ⟨hcosb, hvalb⟩ := hval z h₁ hq hcos₁
  rw [genLowerValue_eq_of_mem M 𝔪 h₁]
  refine (congrArg (fun l : Λ => (l : WithTop Λ)) hvalb.symm).trans ?_
  -- (ii) re-basing the companion ideal across the empty restricted tower `P|_W`
  have he : IsEmptyTower (restrict (ordMask 𝔪 o) P) := (isEmptyTower_restrict_iff _ P).mpr hMt
  have hEq := restrictEquiv_companionOf_rebase hn h ho P hPt (ordMask 𝔪 o) hMt
  rw [compAt_eq_pullback hn o .refl h] at hdom₁ hmax₁ hcanb hcosb ⊢
  have hdomA := isInvDomain_pullback_val_companionAlong hn hdomP (openPreimage P (ordMask 𝔪 o)) ho
  have hmaxA : IsMaximalOrderAlong
      (MarkedIdeal.pullback (Subtype.val : openPreimage P (ordMask 𝔪 o) → Y₁) (companionOf n (geoTransformAlong 𝔪 P) o)).N
      (MarkedIdeal.pullback (Subtype.val : openPreimage P (ordMask 𝔪 o) → Y₁)
        (companionOf n (geoTransformAlong 𝔪 P) o)).ideal
      (MarkedIdeal.pullback (Subtype.val : openPreimage P (ordMask 𝔪 o) → Y₁) (companionOf n (geoTransformAlong 𝔪 P) o)).d := by
    rw [pullback_val_companionOf hn hdomP.isWellFormed hdomP.isNonzeroAlongAt _ o]
    have hN : (companionOf n (M := CMfd.of (n := n) (openPreimage P (ordMask 𝔪 o)))
        (MarkedIdeal.pullback (Subtype.val : openPreimage P (ordMask 𝔪 o) → Y₁) (geoTransformAlong 𝔪 P)) o).N =
        (MarkedIdeal.pullback (Subtype.val : openPreimage P (ordMask 𝔪 o) → Y₁) (geoTransformAlong 𝔪 P)).N :=
      companionAlong_N _ _ _ _ _ _
    rw [hN]
    refine isMaximalOrderAlong_companionOf_pullback_val hn hdomP _ fun x _ hxA => ?_
    have hxA' : x ∈ ordMask (geoTransformAlong 𝔪 P) o := by rw [ordMask_isEmptyTower hn h o P hP]; exact hxA
    exact (mem_ordMask_iff hn hdomP.isWellFormed hdomP.isNonzeroAlongAt o x).mp hxA'
  have hmax₀ := (StepOneEmptyPrefix.hypotheses_emptyPrefix (MarkedIdeal.pullback
    (Subtype.val : ordMask (geoTransformAlong 𝔪 .refl) o → X) (companionOf n (geoTransformAlong 𝔪 .refl) o))
    hdom₁.isWellFormed hdom₁.one_le_d hmax₁
    hdom₁.dimLE _ he).2.2.1
  obtain ⟨-, -, hvalA⟩ := hM.value_rebase hdom₁ hmax₁ _ he hEq hdomA.isWellFormed.isCoherent hmaxA hmax₀
    (restrict (openPreimage P (ordMask 𝔪 o)) T₁) hcanb
  refine (congrArg (fun l : Λ => (l : WithTop Λ)) (hvalA _ hcosb)).trans ?_
  -- (iii) the mask of `𝔪_P` is the preimage of that of `𝔪`
  rw [pullback_val_companionOf hn hdomP.isWellFormed hdomP.isNonzeroAlongAt _ o]
  classical
  let F : Opens Y₁ → WithTop Λ := fun B =>
    if hB : T₁.proj z ∈ B then
      ((M (companionOf n (M := CMfd.of (n := n) B) (MarkedIdeal.pullback (Subtype.val : B → Y₁) (geoTransformAlong 𝔪 P)) o)
        (restrict B T₁) (⟨z, hB⟩ : openPreimage T₁ B) : Λ) : WithTop Λ)
    else ⊤
  have hR : genLowerValue M 𝔪 o P T₁ z = F (ordMask (geoTransformAlong 𝔪 P) o) := rfl
  rw [hR, ordMask_isEmptyTower hn h o P hP]
  simp only [F]
  rw [dif_pos (show T₁.proj z ∈ openPreimage P (ordMask 𝔪 o) from hq)]
  rfl

/-! ### Property (4') of the general value -/

/-- **Property (4') of the general value at positive order**: for `𝔪` in the domain (`0 < n`), `P` a tower with only empty
centres and `P T₁` a canonical segment of the general value which is a multiple test blow-up, at a point `z` of the cosupport of
positive order, the general value of `𝔪` along `P T₁` is that of `𝔪_P` along `T₁`. -/
theorem genInv_emptyPrefix_of_pos (hM : IsMaxOrderValue n k M) (hn : 0 < n) {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) {Y₁ Y : CMfd.{u} n} (P : BlowupTower X Y₁) (hP : IsEmptyTower P) (T₁ : BlowupTower Y₁ Y)
    (hT : IsGeoTestTower 𝔪 (P.append T₁)) (hcan : IsCanonical 𝔪 (genInv M 𝔪) (P.append T₁)) {z : Y}
    (hz : z ∈ (geoTransformAlong 𝔪 (P.append T₁)).cosupp) (hpos : 0 < nmOrd (geoTransformAlong 𝔪 (P.append T₁)) z) :
    genInv M 𝔪 (P.append T₁) z = genInv M (geoTransformAlong 𝔪 P) T₁ z := by
  obtain ⟨o, ho⟩ : ∃ o, nmOrd (geoTransformAlong 𝔪 (P.append T₁)) z = o := ⟨_, rfl⟩
  have ho1 : 1 ≤ o := by omega
  have ho0 : o ≠ 0 := by omega
  have ho' : nmOrd (geoTransformAlong (geoTransformAlong 𝔪 P) T₁) z = o := by rwa [← geoTransformAlong_append]
  have hz' : z ∈ (geoTransformAlong (geoTransformAlong 𝔪 P) T₁).cosupp := by rwa [← geoTransformAlong_append]
  have hD := hasGenLowerData_of_isCanonical M hM hn h _ hT hcan z hz o ho ho1
  rw [genInv_of_nmOrd_ne_zero M 𝔪 _ ho ho0, genInv_of_nmOrd_ne_zero M _ T₁ ho' ho0]
  -- the regimes along `P H` and along `H` correspond
  have hG : ∀ {Y₀ Z : CMfd.{u} n} (T : BlowupTower Y₁ Y₀) (C : Set Y₀) (π : Z → Y₀) (hπ : IsBlowupAlong n C π),
      True → True := fun _ _ _ _ h => h
  have hQ : ∀ {Y₀ : CMfd.{u} n} (H₀ : BlowupTower Y₁ Y₀) (y : Y₀), True →
      (OrdRegime 𝔪 o (P.append H₀) y ↔ OrdRegime (geoTransformAlong 𝔪 P) o H₀ y) :=
    fun H₀ y _ => ordRegime_append_iff 𝔪 o P H₀ y
  rcases (regimeRun_le_length (OrdRegime (geoTransformAlong 𝔪 P) o) T₁ z).lt_or_eq with hlt | heq
  · -- the run stays inside `T₁`: both companion values are computed from the same transform
    have hr := regimeRun_append_of_lt (OrdRegime 𝔪 o) (OrdRegime (geoTransformAlong 𝔪 P) o) P (fun _ => True) hG hQ
      T₁ z trivial hlt
    rw [hr]
    simp only [head, tail]
    rw [split_append_of_le P T₁ _ hlt.le]
    dsimp only
    rw [GeneralRepresentative.genLowerValue_congr_of_eq M (𝔫 := geoTransformAlong 𝔪 P) o
      (geoTransformAlong_append 𝔪 P _)]
  · -- the run covers `T₁`, then all of `P`
    have hreg' : OrdRegime (geoTransformAlong 𝔪 P) o T₁ z := ⟨hz', ho'⟩
    have hbase := regime_base_of_regimeRun_eq (OrdRegime (geoTransformAlong 𝔪 P) o) T₁ z hreg' heq
    have hbaseP : OrdRegime 𝔪 o P (T₁.proj z) := (ordRegime_append_iff 𝔪 o P .refl (T₁.proj z)).mpr hbase
    have hbase0 : OrdRegime 𝔪 o .refl (P.proj (T₁.proj z)) :=
      (ordRegime_isEmptyTower_iff hn h o P hP (T₁.proj z)).mp hbaseP
    have hrP : regimeRun (OrdRegime 𝔪 o) P (T₁.proj z) = P.length := by
      rw [regimeRun_ordRegime_isEmptyTower hn h o P hP, if_pos hbase0]
    have hr := regimeRun_append_of_eq (OrdRegime 𝔪 o) (OrdRegime (geoTransformAlong 𝔪 P) o) P (fun _ => True) hG hQ
      T₁ z trivial heq
    rw [hr, hrP] at hD ⊢
    rw [heq]
    simp only [head, tail] at hD ⊢
    rw [split_of_length_le (P.append T₁) _ (by rw [BlowupTower.length_append]; omega)] at hD ⊢
    rw [split_of_length_le T₁ _ le_rfl]
    dsimp only at hD ⊢
    rw [genLowerValue_refl_append_of_isEmptyTower hM hn h ho1 P hP T₁ hD]
    rfl

/-- **Property (4') of the general value in the shape of the field `emptyPrefix`** of
`ResolutionInvariantExt.ResolutionInvariant`: along canonical segments of the general value (`M` a value function
for the marked ideals of maximal order, `0 < n`), at every point (order `0`:
`GeneralValueOrderZero.emptyPrefix_field_of_nmOrd_eq_zero`). -/
theorem emptyPrefix_field (hM : IsMaxOrderValue n k M) (hn : 0 < n) (𝔪 : MarkedIdeal n X) (h : IsInvDomain k 𝔪)
    {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (h₀ : IsEmptyTower T₀)
    (hcan : IsCanonical 𝔪 (genInv M 𝔪) (T₀.append T₁)) (z : Y) (hz : z ∈ (geoTransformAlong 𝔪 (T₀.append T₁)).cosupp) :
    genInv M 𝔪 (T₀.append T₁) z = genInv M (geoTransformAlong 𝔪 T₀) T₁ z := by
  rcases Nat.eq_zero_or_pos (nmOrd (geoTransformAlong 𝔪 (T₀.append T₁)) z) with h0 | hpos
  · exact GeneralValueOrderZero.emptyPrefix_field_of_nmOrd_eq_zero M 𝔪 T₀ T₁ h₀ hcan z hz h0
  · exact genInv_emptyPrefix_of_pos hM hn h T₀ h₀ T₁
      (GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn h _ hcan) hcan hz hpos

end

end Hironaka.GeneralEmptyPrefix
