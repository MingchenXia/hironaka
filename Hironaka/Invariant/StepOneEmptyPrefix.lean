/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneAdmissible
import Hironaka.Invariant.ContactEmptyPrefix
import Hironaka.Invariant.ContactRepresentative
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.BoundaryCount
import Hironaka.MarkedIdeal.CodimOneSupportAlong
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Invariant.ContactCanonicalAlong
import Hironaka.Invariant.ContactLowerValue
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Invariant.InvDomainMemberRestriction
import Hironaka.Invariant.InvDomainRebase
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneCanonicalTail
import Hironaka.Invariant.StepOneCompare
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.Invariant.StepOneRegime
import Hironaka.Invariant.StepOneValue
import Hironaka.Invariant.StepOneValueMasked
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1: the value re-based across an empty prefix (property (4'))

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`: resolutions are compatible with
*extensions* (isomorphisms inserted into the sequence), here blowups along the empty set at the start.

## Main results

* `boundaryCount_append_of_forall_notMem`, `memberInterLocus_append_of_forall_eq_empty`,
  `membersThrough_append_of_forall_eq_empty`: empty members do not count;
* `drop_E_geoTransformAlong_of_isEmptyTower`, `strictAlong_empty`: the exceptional members of an empty tower are empty;
* `restrictEquiv_barMarked_append`: `J̄(𝔍_P)_{H₀} ≃ J̄(𝔍)_{P H₀}` along every multiple test blow-up `P H₀`;
* `origMembers_emptyPrefix`, `level_emptyPrefix`, `isSpecial_emptyPrefix_iff`, `stepRegime_emptyPrefix_iff`,
  `maskA_emptyPrefix`: the original members of `𝔍_P` are those of `𝔍` followed by empty sets; levels, special points,
  regimes and the masks of Step 1ab agree;
* `restrictEquiv_memberRestrict_membersThrough`, `lowerData_congr`: Step 1ab's restricted marked ideals of
  restricted-equivalent marked ideals, and lower data across them;
* `lowerDataL_succ_emptyPrefix`, `lowerValueL_succ_emptyPrefix_refl`: Step 1ab's lower data and lower value across
  an empty prefix (the run inside the tail, and the run covering it) -- the twins of
  `ContactLowerValue.lowerValueL_zero_emptyPrefix` and `lowerValueL_zero_emptyPrefix_rebase` (Step 1bb);
* `regimeRun_append_of_lt`, `regimeRun_append_of_eq`, `regime_base_of_regimeRun_eq`, `regimeRun_eq_length_of_isEmptyTower`,
  `split_zero`, `split_append_of_le`, `split_of_length_le`: the run cap -- a run along `P T₁` is the run along `T₁` if shorter
  than `T₁`, and otherwise covers `P` too (empty steps keep the regime);
* `hypotheses_emptyPrefix`, `stepOneInvM_emptyPrefix_eq`, **`stepOneInvM_emptyPrefix`**: property (4').
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneEmptyPrefix

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime Hironaka.StepOneValue Hironaka.StepOneLowerDomain Hironaka.StepOneMaskTower Hironaka.StepOneValueMasked Hironaka.StepOneCanonicalTail Hironaka.BoundaryCount Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen Hironaka.HomogenizedIdealAlong Hironaka.CodimOneSupportAlong Hironaka.MemberInterLocusAlong Hironaka.InvDomainMemberRestriction Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
open Hironaka.HomogenizedGlueingTower (strictAlong strictAlong_step)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant IsEmptyTower isGeoTestTower_of_isEmptyTower isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Lists of members with empty sets appended -/

section Lists

variable {M : Type*} [TopologicalSpace M]

open Classical in
/-- **Empty members do not count**: appending members missing `y` does not change the boundary count at `y`. -/
theorem boundaryCount_append_of_forall_notMem {A L : List (Set M)} {y : M} (hL : ∀ H ∈ L, y ∉ H) :
    boundaryCount (A ++ L) y = boundaryCount A y := by
  unfold boundaryCount
  refine Finset.card_bij' (fun i hi => ⟨i.1, ?_⟩) (fun j _ => ⟨j.1, by rw [List.length_append]; omega⟩) ?_ ?_ ?_ ?_
  · by_contra hlt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.get_eq_getElem] at hi
    rw [List.getElem_append_right (by omega)] at hi
    exact hL _ (List.getElem_mem _) hi
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.get_eq_getElem] at hi ⊢
    rwa [List.getElem_append_left] at hi
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.get_eq_getElem] at hj ⊢
    rwa [List.getElem_append_left]
  · intro i hi
    rfl
  · intro j hj
    rfl

/-- **Empty members do not change the member locus.** -/
theorem memberInterLocus_append_of_forall_eq_empty (N S : Set M) {A L : List (Set M)} (hL : ∀ H ∈ L, H = ∅) :
    memberInterLocus N (A ++ L) S = memberInterLocus N A S := by
  ext x
  simp only [memberInterLocus, mem_ofPred_eq]
  refine and_congr_right fun _ => Filter.eventually_congr (Eventually.of_forall fun y => ?_)
  refine imp_congr_right fun _ => imp_congr_left ?_
  rw [forall_get_iff (P := fun H => x ∈ H → y ∈ H), forall_get_iff (P := fun H => x ∈ H → y ∈ H)]
  refine ⟨fun h H hH hxH => h H (List.mem_append_left _ hH) hxH, fun h H hH hxH => ?_⟩
  rcases List.mem_append.mp hH with hH | hH
  · exact h H hH hxH
  · rw [hL H hH] at hxH
    exact absurd hxH (notMem_empty x)

end Lists

/-! ### The divisor of a transform along a tower with only empty centres -/

section Divisor

variable {X : CMfd.{u} n}

/-- **The exceptional members of a tower with only empty centres are empty.** -/
theorem drop_E_geoTransformAlong_of_isEmptyTower (𝔪 : MarkedIdeal n X) :
    ∀ {Y : CMfd.{u} n} (P : BlowupTower X Y), IsEmptyTower P →
      ∀ H ∈ (geoTransformAlong 𝔪 P).E.drop 𝔪.E.length, H = ∅
  | _, .refl, _, H, hH => by
      simp at hH
  | _, .step P C π hπ, hP, H, hH => by
      obtain ⟨hP, hC⟩ : IsEmptyTower P ∧ C = ∅ := hP
      subst hC
      have hlen : 𝔪.E.length ≤ ((geoTransformAlong 𝔪 P).E.map (BlowupStrictSubmanifold.geoStrictTransform π ∅)).length := by
        rw [List.length_map, length_E_geoTransformAlong]; omega
      rw [geoTransformAlong_step, geoTransform_E, List.drop_append_of_le_length hlen, ← List.map_drop] at hH
      rcases List.mem_append.mp hH with hH | hH
      · obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
        rw [drop_E_geoTransformAlong_of_isEmptyTower 𝔪 P hP H₀ hH₀]
        simp [BlowupStrictSubmanifold.geoStrictTransform]
      · rw [List.mem_singleton.mp hH, preimage_empty]

/-- The strict transform of the empty set is empty. -/
theorem strictAlong_empty : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), strictAlong T (∅ : Set X) = ∅
  | _, .refl => rfl
  | _, .step T C π hπ => by
      rw [strictAlong_step, strictAlong_empty T]
      simp [BlowupStrictSubmanifold.geoStrictTransform]

end Divisor

/-! ### The marked ideal of Step 1 re-based across an empty prefix -/

section Rebase

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **`J̄(𝔍_P)_{H₀} ≃ J̄(𝔍)_{P H₀}`** along every multiple test blow-up `P H₀` of `J̄` with `P` empty (`𝔍` well formed,
`d ≥ 1`): `ContactEmptyPrefix.restrictEquiv_barMarked_geoTransformAlong_of_isEmptyTower` at the start, then
restricted-equivalent marked ideals have the same transform (`RestrictEquiv.geoTransform_eq`). -/
theorem restrictEquiv_barMarked_append (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y₁ : CMfd.{u} n}
    (P : BlowupTower X Y₁) (hP : IsEmptyTower P) :
    ∀ {Y₀ : CMfd.{u} n} (H₀ : BlowupTower Y₁ Y₀), IsGeoTestTower (barMarked 𝔍) (P.append H₀) →
      RestrictEquiv (geoTransformAlong (barMarked (geoTransformAlong 𝔍 P)) H₀)
        (geoTransformAlong (barMarked 𝔍) (P.append H₀))
  | _, .refl, _ => ContactEmptyPrefix.restrictEquiv_barMarked_geoTransformAlong_of_isEmptyTower 𝔍
      h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd P hP
  | _, .step H₀ C π hπ, hT => by
      have hT' : IsGeoTestTower (barMarked 𝔍) (P.append H₀) := hT.1
      have ih := restrictEquiv_barMarked_append h𝔍 hd P hP H₀ hT'
      have hJ := isWellFormed_barMarked 𝔍 h𝔍
      obtain ⟨-, hc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent _ hT'
      have hPt : IsGeoTestTower 𝔍 P := isGeoTestTower_of_isEmptyTower 𝔍 P hP
      have hJ' := isWellFormed_barMarked _ (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔍 P hPt)
      have hT₀' : IsGeoTestTower (barMarked (geoTransformAlong 𝔍 P)) H₀ :=
        (ContactEmptyPrefix.isGeoTestTower_barMarked_geoTransformAlong_iff 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd P
          hP H₀).mpr hT'
      obtain ⟨hN', hc'⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ'.isClosedSubmanifold_N
        hJ'.isCoherent _ hT₀'
      have heq := ih.geoTransform_eq hN'.1 hc' hc (C := C) hπ.contMDiff
      show RestrictEquiv ((geoTransformAlong (barMarked (geoTransformAlong 𝔍 P)) H₀).geoTransform C π)
        ((geoTransformAlong (barMarked 𝔍) (P.append H₀)).geoTransform C π)
      rw [heq]
      obtain ⟨-, hc''⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent _ hT
      exact RestrictEquiv.refl hc''

/-- **The original members of `𝔍_P`** along `H₀` are those of `𝔍` along `P H₀` followed by empty sets (the exceptional
members of `P`). -/
theorem origMembers_emptyPrefix {Y₁ : CMfd.{u} n} (P : BlowupTower X Y₁) (hP : IsEmptyTower P) {Y₀ : CMfd.{u} n}
    (H₀ : BlowupTower Y₁ Y₀) :
    ∃ L : List (Set Y₀), (∀ H ∈ L, H = ∅) ∧
      origMembers (geoTransformAlong 𝔍 P) H₀ = origMembers 𝔍 (P.append H₀) ++ L := by
  refine ⟨((geoTransformAlong 𝔍 P).E.drop 𝔍.E.length).map (strictAlong H₀), ?_, ?_⟩
  · intro H hH
    obtain ⟨H₀', hH₀', rfl⟩ := List.mem_map.mp hH
    rw [drop_E_geoTransformAlong_of_isEmptyTower 𝔍 P hP H₀' hH₀', strictAlong_empty]
  · have hsplit : (geoTransformAlong 𝔍 P).E =
        𝔍.E.map (strictAlong P) ++ (geoTransformAlong 𝔍 P).E.drop 𝔍.E.length := by
      rw [← MemberInterTowerAlong.take_E_geoTransformAlong]
      exact (List.take_append_drop _ _).symm
    rw [origMembers_eq, origMembers_eq]
    conv_lhs => rw [hsplit]
    rw [List.map_append, List.map_map]
    congr 1
    exact List.map_congr_left fun H _ => (MemberInterLocusAlong.strictAlong_append P H H₀).symm

/-- **The levels agree.** -/
theorem level_emptyPrefix {Y₁ : CMfd.{u} n} (P : BlowupTower X Y₁) (hP : IsEmptyTower P) {Y₀ : CMfd.{u} n}
    (H₀ : BlowupTower Y₁ Y₀) (y : Y₀) : level (geoTransformAlong 𝔍 P) H₀ y = level 𝔍 (P.append H₀) y := by
  obtain ⟨L, hL, hE⟩ := origMembers_emptyPrefix 𝔍 P hP H₀
  unfold level
  rw [hE]
  exact boundaryCount_append_of_forall_notMem fun H hH hyH => by rw [hL H hH] at hyH; exact hyH

/-- **The special points agree** (along a multiple test blow-up `P H₀` of `J̄`). -/
theorem isSpecial_emptyPrefix_iff (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y₁ : CMfd.{u} n} (P : BlowupTower X Y₁)
    (hP : IsEmptyTower P) {Y₀ : CMfd.{u} n} (H₀ : BlowupTower Y₁ Y₀) (hT : IsGeoTestTower (barMarked 𝔍) (P.append H₀))
    (y : Y₀) : IsSpecial (geoTransformAlong 𝔍 P) H₀ y ↔ IsSpecial 𝔍 (P.append H₀) y := by
  have hEq := restrictEquiv_barMarked_append 𝔍 h𝔍 hd P hP H₀ hT
  obtain ⟨L, hL, hE⟩ := origMembers_emptyPrefix 𝔍 P hP H₀
  have hcos := hEq.cosupp_eq
  unfold IsSpecial
  rw [level_emptyPrefix 𝔍 P hP H₀ y, hE, memberInterLocus_append_of_forall_eq_empty _ _ hL, hcos, hEq.N_eq]
  unfold codimOnePartAlong
  have hco : GermIdealOrder.cosupport n (geoTransformAlong (barMarked 𝔍) (P.append H₀)).N
      (geoTransformAlong (barMarked (geoTransformAlong 𝔍 P)) H₀).ideal
      (geoTransformAlong (barMarked (geoTransformAlong 𝔍 P)) H₀).d =
      GermIdealOrder.cosupport n (geoTransformAlong (barMarked 𝔍) (P.append H₀)).N
        (geoTransformAlong (barMarked 𝔍) (P.append H₀)).ideal (geoTransformAlong (barMarked 𝔍) (P.append H₀)).d := by
    have := hcos
    unfold MarkedIdeals.MarkedIdeal.cosupp at this
    rwa [hEq.N_eq] at this
  rw [hco]

/-- **The regimes agree.** -/
theorem stepRegime_emptyPrefix_iff (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y₁ : CMfd.{u} n} (P : BlowupTower X Y₁)
    (hP : IsEmptyTower P) {Y₀ : CMfd.{u} n} (H₀ : BlowupTower Y₁ Y₀) (hT : IsGeoTestTower (barMarked 𝔍) (P.append H₀))
    (s : ℕ) (y : Y₀) : stepRegime (geoTransformAlong 𝔍 P) s H₀ y ↔ stepRegime 𝔍 s (P.append H₀) y := by
  unfold stepRegime
  rw [level_emptyPrefix 𝔍 P hP H₀ y, isSpecial_emptyPrefix_iff 𝔍 h𝔍 hd P hP H₀ hT y]

/-- **The masks of Step 1ab agree.** -/
theorem maskA_emptyPrefix (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y₁ : CMfd.{u} n} (P : BlowupTower X Y₁)
    (hP : IsEmptyTower P) {Y₀ : CMfd.{u} n} (H₀ : BlowupTower Y₁ Y₀) (hT : IsGeoTestTower (barMarked 𝔍) (P.append H₀))
    (y₀ : Y₀) : maskA (geoTransformAlong 𝔍 P) H₀ y₀ = maskA 𝔍 (P.append H₀) y₀ := by
  obtain ⟨L, hL, hE⟩ := origMembers_emptyPrefix 𝔍 P hP H₀
  apply Opens.ext
  show interior _ = interior _
  congr 1
  ext z
  simp only [mem_ofPred_eq]
  rw [hE, level_emptyPrefix 𝔍 P hP H₀ z, level_emptyPrefix 𝔍 P hP H₀ y₀, isSpecial_emptyPrefix_iff 𝔍 h𝔍 hd P hP H₀ hT z]
  refine and_congr_left fun _ => ⟨fun h H hH hzH => h H (List.mem_append_left _ hH) hzH, fun h H hH hzH => ?_⟩
  rcases List.mem_append.mp hH with hH | hH
  · exact h H hH hzH
  · rw [hL H hH] at hzH
    exact absurd hzH (notMem_empty z)

end Rebase

/-! ### Step 1ab's lower marked ideal re-based across an empty prefix -/

section Lower

/-- **Empty members do not change `S(y)`.** -/
theorem membersThrough_append_of_forall_eq_empty {M : Type*} [TopologicalSpace M] (E E₀ L : List (Set M)) (hL : ∀ H ∈ L, H = ∅) (y : M) :
    membersThrough E (E₀ ++ L) y = membersThrough E E₀ y := by
  ext i
  rw [mem_membersThrough, mem_membersThrough, List.mem_append]
  refine and_congr_left fun hy => or_iff_left fun hH => ?_
  rw [hL _ hH] at hy
  exact notMem_empty y hy

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Step 1ab's restricted marked ideals of restricted-equivalent marked ideals are restricted-equivalent** (coherent
ideals): `𝓢(𝔪, y) ≃ 𝓢(𝔫, y)` for `𝔪 ≃ 𝔫` and the same list `E₀` (`ContactCanonicalAlong.restrictEquiv_coeffMarkedAlong`,
`restrictEquiv_withN`, and `N`, `E` by value). -/
theorem restrictEquiv_memberRestrict_membersThrough {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) (E₀ : List (Set M)) (y : M) :
    RestrictEquiv (memberRestrict 𝔪 (membersThrough 𝔪.E E₀ y)) (memberRestrict 𝔫 (membersThrough 𝔫.E E₀ y)) := by
  have hc := ContactCanonicalAlong.restrictEquiv_coeffMarkedAlong h
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔪) (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔫)
  have hw := ContactCanonicalAlong.restrictEquiv_withN hc
    (A := 𝔪.N ∩ memberInter 𝔪.E (membersThrough 𝔪.E E₀ y)) inter_subset_left
  refine ⟨?_, ?_, hw.d_eq, hw.le, hw.ge⟩
  · rw [InvDomainRebase.memberRestrict_membersThrough_N, InvDomainRebase.memberRestrict_membersThrough_N, h.N_eq, h.E_eq]
  · rw [InvDomainRebase.memberRestrict_membersThrough_E, InvDomainRebase.memberRestrict_membersThrough_E, h.E_eq]

end Lower

section LowerData

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Lower data across restricted-equivalent marked ideals on equal open sets** (generic): if `𝔐' ≃ 𝔐` on `Y₀`, `W' = W`, and
`𝔐'|_{W'}` lies in the domain of `R` with `T₁|_{W'}` a canonical segment and `z` in the cosupport, then the same holds for
`𝔐|_W` and the values agree (`R.representative`). -/
theorem lowerData_congr (R : ResolutionInvariant.{u, v} n k Λ) {Y₀ Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y)
    {W W' : Opens Y₀} (hW : W' = W) {𝔐 𝔐' : MarkedIdeal n Y₀} (hEq : RestrictEquiv 𝔐' 𝔐)
    (h𝔐 : 𝔐.ideal.IsCoherent) {z : Y} (hz' : T₁.proj z ∈ W')
    (hdom' : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W' → Y₀) 𝔐'))
    (hcan' : IsCanonical (MarkedIdeal.pullback (Subtype.val : W' → Y₀) 𝔐')
      (R.inv (MarkedIdeal.pullback (Subtype.val : W' → Y₀) 𝔐')) (restrict W' T₁))
    (hcos' : (⟨z, hz'⟩ : openPreimage T₁ W') ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W' → Y₀) 𝔐') (restrict W' T₁)).cosupp)
    (h𝔐' : 𝔐'.ideal.IsCoherent) :
    ∃ hz : T₁.proj z ∈ W, IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝔐) ∧
      IsCanonical (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝔐)
        (R.inv (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝔐)) (restrict W T₁) ∧
      (⟨z, hz⟩ : openPreimage T₁ W) ∈
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝔐) (restrict W T₁)).cosupp ∧
      R.inv (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝔐) (restrict W T₁) ⟨z, hz⟩ =
        R.inv (MarkedIdeal.pullback (Subtype.val : W' → Y₀) 𝔐') (restrict W' T₁) ⟨z, hz'⟩ := by
  subst hW
  have hE := ContactRepresentative.restrictEquiv_pullback_val W' hEq h𝔐' h𝔐
  have hcW : (MarkedIdeal.pullback (Subtype.val : W' → Y₀) 𝔐).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val h𝔐
  have hdom := InvDomainRebase.isInvDomain_of_restrictEquiv hdom' hE hcW
  have hcan := InvDomainRebase.isCanonical_of_restrictEquiv R hdom' hdom hE _ hcan'
  have hcos := (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong hE
    hdom'.isWellFormed.isClosedSubmanifold_N.1 hdom'.isWellFormed.isCoherent hcW (restrict W' T₁)).1
  refine ⟨hz', hdom, hcan, hcos ▸ hcos', (R.representative _ _ hdom' hdom hE _ hcan' _ hcos').symm⟩

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) (R : ResolutionInvariant.{u, v} n k Λ)

/-- **Step 1ab's lower data and lower value across an empty prefix**: for `P` empty, if the image of `z` has lower data for
`𝔍_P` at the split `(H₀, T₁)`, it has lower data for `𝔍` at the split `(P H₀, T₁)` and the lower values agree (the masks agree,
`maskA_emptyPrefix`, and the restricted marked ideals are restricted-equivalent: `restrictEquiv_barMarked_append`, the original
members of `𝔍_P` being those of `𝔍` followed by empty sets). -/
theorem lowerDataL_succ_emptyPrefix (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n) {Y₁ : CMfd.{u} n}
    (P : BlowupTower X Y₁) (hP : IsEmptyTower P) {Y₀ Y : CMfd.{u} n} (H₀ : BlowupTower Y₁ Y₀) (T₁ : BlowupTower Y₀ Y)
    (hT : IsGeoTestTower (barMarked 𝔍) ((P.append H₀).append T₁)) {s : ℕ} {z : Y}
    (hD' : LowerDataL R (geoTransformAlong 𝔍 P) (lowerMarkedM (geoTransformAlong 𝔍 P)) (s + 1) H₀ T₁ z) :
    LowerDataL R 𝔍 (lowerMarkedM 𝔍) (s + 1) (P.append H₀) T₁ z ∧
      lowerValueL R 𝔍 (lowerMarkedM 𝔍) (s + 1) (P.append H₀) T₁ z =
        lowerValueL R (geoTransformAlong 𝔍 P) (lowerMarkedM (geoTransformAlong 𝔍 P)) (s + 1) H₀ T₁ z := by
  obtain ⟨h', hdom', hcan', hcos'⟩ := hD'
  have hT₀ : IsGeoTestTower (barMarked 𝔍) (P.append H₀) := ((isGeoTestTower_append_iff _ _ T₁).mp hT).1
  have hW := maskA_emptyPrefix 𝔍 h𝔍 hd P hP H₀ hT₀ (T₁.proj z)
  have hEqJ := restrictEquiv_barMarked_append 𝔍 h𝔍 hd P hP H₀ hT₀
  obtain ⟨L, hL, hE⟩ := origMembers_emptyPrefix 𝔍 P hP H₀
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ _ hT₀
  have hPt : IsGeoTestTower 𝔍 P := isGeoTestTower_of_isEmptyTower 𝔍 P hP
  have hJ' := isWellFormed_barMarked _ (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔍 P hPt)
  have hT₀' : IsGeoTestTower (barMarked (geoTransformAlong 𝔍 P)) H₀ :=
    (ContactEmptyPrefix.isGeoTestTower_barMarked_geoTransformAlong_iff 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd P
      hP H₀).mpr hT₀
  have hwf' := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ' _ hT₀'
  have hEqM : RestrictEquiv
      (memberRestrict (geoTransformAlong (barMarked (geoTransformAlong 𝔍 P)) H₀)
        (membersThrough (geoTransformAlong (barMarked (geoTransformAlong 𝔍 P)) H₀).E
          (origMembers (geoTransformAlong 𝔍 P) H₀) (T₁.proj z)))
      (memberRestrict (geoTransformAlong (barMarked 𝔍) (P.append H₀))
        (membersThrough (geoTransformAlong (barMarked 𝔍) (P.append H₀)).E (origMembers 𝔍 (P.append H₀)) (T₁.proj z))) := by
    rw [hE, membersThrough_append_of_forall_eq_empty _ _ _ hL]
    exact restrictEquiv_memberRestrict_membersThrough hEqJ hwf'.isCoherent hwf.isCoherent _ _
  obtain ⟨hz, hdom, hcan, hcos, hval⟩ := lowerData_congr R T₁ hW hEqM
    (isWellFormed_memberRestrict hn hwf _).isCoherent h' hdom' hcan' hcos'
    (isWellFormed_memberRestrict hn hwf' _).isCoherent
  refine ⟨⟨hz, hdom, hcan, hcos⟩, ?_⟩
  rw [lowerValueL_eq_of_mem R 𝔍 _ (s := s + 1) (T₀ := P.append H₀) hz,
    lowerValueL_eq_of_mem R (geoTransformAlong 𝔍 P) _ h']
  exact congrArg _ hval

/-- **Step 1ab's lower value across an empty prefix, when the run reaches into it** (case of the full run): the lower value of
`𝔍` along `P T₁` from the base equals that of `𝔍_P` along `T₁` from its base -- re-basing within `𝔍` across `P`, whose
centres are empty (`StepOneCompare.lowerValue_eq_succ`), then `lowerDataL_succ_emptyPrefix` at `H₀ = refl`. -/
theorem lowerValueL_succ_emptyPrefix_refl (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n) {Y₁ : CMfd.{u} n}
    (P : BlowupTower X Y₁) (hP : IsEmptyTower P) {Y : CMfd.{u} n} (T₁ : BlowupTower Y₁ Y)
    (hT : IsGeoTestTower (barMarked 𝔍) (P.append T₁)) {s : ℕ} {z : Y}
    (hD : LowerDataL R 𝔍 (lowerMarkedM 𝔍) (s + 1) .refl (P.append T₁) z)
    (hD' : LowerDataL R (geoTransformAlong 𝔍 P) (lowerMarkedM (geoTransformAlong 𝔍 P)) (s + 1) .refl T₁ z) :
    lowerValueL R 𝔍 (lowerMarkedM 𝔍) (s + 1) .refl (P.append T₁) z =
      lowerValueL R (geoTransformAlong 𝔍 P) (lowerMarkedM (geoTransformAlong 𝔍 P)) (s + 1) .refl T₁ z := by
  obtain ⟨⟨h₁, hdom₁, hcan₁, hcos₁⟩, hval₁⟩ := lowerDataL_succ_emptyPrefix 𝔍 R h𝔍 hd hn P hP .refl T₁ hT hD'
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hPJ : IsGeoTestTower (barMarked 𝔍) P := ((isGeoTestTower_append_iff _ _ T₁).mp hT).1
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ _ hPJ
  have hcoh : (memberRestrict (geoTransformAlong (barMarked 𝔍) P)
      (membersThrough (geoTransformAlong (barMarked 𝔍) P).E (origMembers 𝔍 P) (T₁.proj z))).ideal.IsCoherent :=
    (isWellFormed_memberRestrict hn hwf _).isCoherent
  have hWe : lowerMask 𝔍 (s + 1) P (T₁.proj z) =
      lowerMask 𝔍 (s + 1) ((BlowupTower.refl : BlowupTower X X).append P) (T₁.proj z) := by
    rw [BlowupTower.refl_append]
  have hEqR : RestrictEquiv
      (memberRestrict (geoTransformAlong (barMarked 𝔍) P)
        (membersThrough (geoTransformAlong (barMarked 𝔍) P).E (origMembers 𝔍 P) (T₁.proj z)))
      (memberRestrict (geoTransformAlong (barMarked 𝔍) ((BlowupTower.refl : BlowupTower X X).append P))
        (membersThrough (geoTransformAlong (barMarked 𝔍) ((BlowupTower.refl : BlowupTower X X).append P)).E
          (origMembers 𝔍 ((BlowupTower.refl : BlowupTower X X).append P)) (T₁.proj z))) := by
    rw [BlowupTower.refl_append]
    exact RestrictEquiv.refl hcoh
  have hcoh' : (memberRestrict (geoTransformAlong (barMarked 𝔍) ((BlowupTower.refl : BlowupTower X X).append P))
      (membersThrough (geoTransformAlong (barMarked 𝔍) ((BlowupTower.refl : BlowupTower X X).append P)).E
        (origMembers 𝔍 ((BlowupTower.refl : BlowupTower X X).append P)) (T₁.proj z))).ideal.IsCoherent := by
    rw [BlowupTower.refl_append]
    exact hcoh
  obtain ⟨h₂, hdom₂, hcan₂, hcos₂, hval₂⟩ := lowerData_congr R T₁ hWe hEqR hcoh' h₁ hdom₁ hcan₁ hcos₁ hcoh
  have key := StepOneCompare.lowerValue_eq_succ R 𝔍 h𝔍 hn .refl P T₁ (by rw [BlowupTower.refl_append]; exact hT)
    hdom₂ hcan₂ h₂ rfl hcos₂ hD (ContactLowerValue.centresAvoid_of_isEmptyTower _ P hP)
  rw [key]
  calc _ = ((R.inv (lowerMarkedM 𝔍 (s + 1) P (T₁.proj z)) (restrict (lowerMask 𝔍 (s + 1) P (T₁.proj z)) T₁)
        ⟨z, h₁⟩ : Λ) : WithTop Λ) := congrArg _ hval₂
    _ = lowerValueL R 𝔍 (lowerMarkedM 𝔍) (s + 1) P T₁ z :=
        (lowerValueL_eq_of_mem R 𝔍 _ (s := s + 1) (T₀ := P) h₁).symm
    _ = _ := hval₁

end LowerData

/-! ### Regime runs and splits along a concatenation -/

section Run

variable {X : CMfd.{u} n} {Y₁ : CMfd.{u} n}

/-- **Runs along `P T₁` that stay inside `T₁`**: for regimes `Q` along towers over `X` and `Q'` along towers over `Y₁` with
`Q (P H₀) ↔ Q' H₀` on the towers `H₀` with a property `G` inherited by prefixes, a run of `Q'` along `T₁` (with `G T₁`) shorter
than `T₁` is the run of `Q` along `P T₁`. -/
theorem regimeRun_append_of_lt (Q : Regime X) (Q' : Regime Y₁) (P : BlowupTower X Y₁)
    (G : ∀ {Y₀ : CMfd.{u} n}, BlowupTower Y₁ Y₀ → Prop)
    (hG : ∀ {Y₀ Z : CMfd.{u} n} (T : BlowupTower Y₁ Y₀) (C : Set Y₀) (π : Z → Y₀) (hπ : IsBlowupAlong n C π),
      G (.step T C π hπ) → G T)
    (hQ : ∀ {Y₀ : CMfd.{u} n} (H₀ : BlowupTower Y₁ Y₀) (y : Y₀), G H₀ → (Q (P.append H₀) y ↔ Q' H₀ y)) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₁ Y) (z : Y), G T₁ → regimeRun Q' T₁ z < T₁.length →
      regimeRun Q (P.append T₁) z = regimeRun Q' T₁ z
  | _, .refl, z, _, h => absurd h (by simp)
  | _, .step T C π hπ, z, hGT, h => by
      have hGT' := hG T C π hπ hGT
      by_cases hq : Q' T (π z)
      · rw [regimeRun_step_of Q' T C π hπ hq] at h ⊢
        rw [BlowupTower.append_step, regimeRun_step_of Q (P.append T) C π hπ ((hQ T (π z) hGT').mpr hq),
          regimeRun_append_of_lt Q Q' P G hG hQ T (π z) hGT' (by rw [BlowupTower.length_step] at h; omega)]
      · rw [regimeRun_step_of_not Q' T C π hπ hq, BlowupTower.append_step,
          regimeRun_step_of_not Q (P.append T) C π hπ (fun h' => hq ((hQ T (π z) hGT').mp h'))]

/-- **Runs along `P T₁` that cover `T₁`** continue into `P`. -/
theorem regimeRun_append_of_eq (Q : Regime X) (Q' : Regime Y₁) (P : BlowupTower X Y₁)
    (G : ∀ {Y₀ : CMfd.{u} n}, BlowupTower Y₁ Y₀ → Prop)
    (hG : ∀ {Y₀ Z : CMfd.{u} n} (T : BlowupTower Y₁ Y₀) (C : Set Y₀) (π : Z → Y₀) (hπ : IsBlowupAlong n C π),
      G (.step T C π hπ) → G T)
    (hQ : ∀ {Y₀ : CMfd.{u} n} (H₀ : BlowupTower Y₁ Y₀) (y : Y₀), G H₀ → (Q (P.append H₀) y ↔ Q' H₀ y)) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₁ Y) (z : Y), G T₁ → regimeRun Q' T₁ z = T₁.length →
      regimeRun Q (P.append T₁) z = T₁.length + regimeRun Q P (T₁.proj z)
  | _, .refl, z, _, _ => by simp
  | _, .step T C π hπ, z, hGT, h => by
      have hGT' := hG T C π hπ hGT
      have hq : Q' T (π z) := by
        by_contra hq
        rw [regimeRun_step_of_not Q' T C π hπ hq, BlowupTower.length_step] at h
        omega
      rw [regimeRun_step_of Q' T C π hπ hq, BlowupTower.length_step] at h
      rw [BlowupTower.append_step, regimeRun_step_of Q (P.append T) C π hπ ((hQ T (π z) hGT').mpr hq),
        regimeRun_append_of_eq Q Q' P G hG hQ T (π z) hGT' (by omega), BlowupTower.length_step, BlowupTower.proj_step]
      simp only [Function.comp_apply]
      omega

/-- **A run covering the tower starts at its base**: if `y` is in the regime at the last stage and its run is the whole
tower, its image at the base is in the regime. -/
theorem regime_base_of_regimeRun_eq (Q' : Regime Y₁) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₁ Y) (z : Y), Q' T₁ z → regimeRun Q' T₁ z = T₁.length →
      Q' (.refl : BlowupTower Y₁ Y₁) (T₁.proj z)
  | _, .refl, _, hz, _ => hz
  | _, .step T C π hπ, z, _, h => by
      have hq : Q' T (π z) := by
        by_contra hq
        rw [regimeRun_step_of_not Q' T C π hπ hq, BlowupTower.length_step] at h
        omega
      rw [regimeRun_step_of Q' T C π hπ hq, BlowupTower.length_step] at h
      exact regime_base_of_regimeRun_eq Q' T (π z) hq (by omega)

/-- **Along a tower whose steps preserve the regime, a run is the whole tower.** -/
theorem regimeRun_eq_length_of_isEmptyTower (Q : Regime X)
    (hQ : ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (π : Z → Y) (hπ : IsBlowupAlong n (∅ : Set Y) π),
      IsEmptyTower T → ∀ z : Z, Q (.step T ∅ π hπ) z → Q T (π z)) :
    ∀ {Y : CMfd.{u} n} (P : BlowupTower X Y), IsEmptyTower P → ∀ y : Y, Q P y → regimeRun Q P y = P.length
  | _, .refl, _, _, _ => rfl
  | _, .step P C π hπ, hP, y, hy => by
      obtain ⟨hP, hC⟩ : IsEmptyTower P ∧ C = ∅ := hP
      subst hC
      have hq := hQ P π hπ hP y hy
      rw [regimeRun_step_of Q P ∅ π hπ hq, regimeRun_eq_length_of_isEmptyTower Q hQ P hP (π y) hq,
        BlowupTower.length_step]

/-- The split at `0` is the tower followed by the empty tail. -/
theorem split_zero {Z₁ : CMfd.{u} n} : ∀ {Y : CMfd.{u} n} (T : BlowupTower Z₁ Y), split T 0 = ⟨Y, T, .refl⟩
  | _, .refl => rfl
  | _, .step _ _ _ _ => rfl

/-- **The split of a concatenation inside its tail.** -/
theorem split_append_of_le (P : BlowupTower X Y₁) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₁ Y) (r : ℕ), r ≤ T₁.length →
      split (P.append T₁) r = ⟨(split T₁ r).1, P.append (head T₁ r), tail T₁ r⟩
  | _, T₁, 0, _ => by
      simp only [head, tail]
      rw [split_zero, split_zero]
  | _, .refl, _ + 1, h => absurd h (by simp)
  | _, .step T C π hπ, j + 1, h => by
      rw [BlowupTower.length_step] at h
      have ih := split_append_of_le P T j (by omega)
      show (⟨(split (P.append T) j).1, (split (P.append T) j).2.1, .step (split (P.append T) j).2.2 C π hπ⟩ :
        Σ Y₀ : CMfd.{u} n, BlowupTower X Y₀ × BlowupTower Y₀ _) = _
      rw [ih]
      rfl

/-- **The split at (or beyond) the length.** -/
theorem split_of_length_le : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ), T.length ≤ j →
    split T j = ⟨X, .refl, T⟩
  | _, .refl, 0, _ => rfl
  | _, .refl, _ + 1, _ => rfl
  | _, .step T C π hπ, 0, h => absurd h (by simp)
  | _, .step T C π hπ, j + 1, h => by
      rw [BlowupTower.length_step] at h
      have ih := split_of_length_le T j (by omega)
      show (⟨(split T j).1, (split T j).2.1, .step (split T j).2.2 C π hπ⟩ :
        Σ Y₀ : CMfd.{u} n, BlowupTower X Y₀ × BlowupTower Y₀ _) = _
      rw [ih]

end Run

/-! ### Property (4') -/

section EmptyPrefix

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **The hypotheses of Step 1 pass to `𝔍_P`** (`P` empty): well formed, `d ≥ 1`, maximal order along `N`, `dim N ≤ k`. -/
theorem hypotheses_emptyPrefix (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (hk : DimLE n 𝔍.N k) {Y₁ : CMfd.{u} n} (P : BlowupTower X Y₁) (hP : IsEmptyTower P) :
    (geoTransformAlong 𝔍 P).IsWellFormed ∧ 1 ≤ (geoTransformAlong 𝔍 P).d ∧
      IsMaximalOrderAlong (geoTransformAlong 𝔍 P).N (geoTransformAlong 𝔍 P).ideal (geoTransformAlong 𝔍 P).d ∧
      DimLE n (geoTransformAlong 𝔍 P).N k := by
  have hPt : IsGeoTestTower 𝔍 P := isGeoTestTower_of_isEmptyTower 𝔍 P hP
  refine ⟨MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔍 P hPt, by rw [d_geoTransformAlong]; exact hd,
    isMaximalOrderAlong_geoTransformAlong h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hmax P hPt,
    InvDomainTowerAlong.dimLE_geoTransformAlong h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hk P hPt⟩

/-- **The values agree along `P T₁` and `T₁`** when both are canonical segments (`P` empty): equal levels and special
points; at a non-special point the run either stays inside `T₁` (same split, `P` prepended to the head:
`ContactLowerValue.lowerValueL_zero_emptyPrefix` at level `0`, `lowerDataL_succ_emptyPrefix` at levels `≥ 1`), or
covers `T₁` and then all of `P` (the base on both sides: `lowerValueL_zero_emptyPrefix_rebase`,
`lowerValueL_succ_emptyPrefix_refl`).
-/
theorem stepOneInvM_emptyPrefix_eq (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y₁ : CMfd.{u} n} (P : BlowupTower X Y₁)
    (hP : IsEmptyTower P) {Y : CMfd.{u} n} (T₁ : BlowupTower Y₁ Y)
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) (P.append T₁))
    (hcan' : IsCanonical (barMarked (geoTransformAlong 𝔍 P)) (stepOneInvM R (geoTransformAlong 𝔍 P)) T₁) {z : Y}
    (hz : z ∈ (geoTransformAlong (barMarked 𝔍) (P.append T₁)).cosupp) :
    stepOneInvM R 𝔍 (P.append T₁) z = stepOneInvM R (geoTransformAlong 𝔍 P) T₁ z := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  obtain ⟨h𝔍', hd', hmax', hk'⟩ := hypotheses_emptyPrefix 𝔍 h𝔍 hd hmax hk P hP
  have hT := StepOneAdmissible.isGeoTestTower_of_isCanonical_stepOneInvM 𝔍 R h𝔍 hd hn hmax hk _ hcan
  have hT' := StepOneAdmissible.isGeoTestTower_of_isCanonical_stepOneInvM _ R h𝔍' hd' hn hmax' hk' _ hcan'
  have hPJ : IsGeoTestTower (barMarked 𝔍) P := ((isGeoTestTower_append_iff _ _ T₁).mp hT).1
  have hEqT := restrictEquiv_barMarked_append 𝔍 h𝔍 hd P hP T₁ hT
  have hz' : z ∈ (geoTransformAlong (barMarked (geoTransformAlong 𝔍 P)) T₁).cosupp := by
    rw [hEqT.cosupp_eq]; exact hz
  have hD := hasLowerDataL_of_isCanonical 𝔍 R h𝔍 hd hn hmax hk _ hT hcan z hz
  have hD' := hasLowerDataL_of_isCanonical _ R h𝔍' hd' hn hmax' hk' _ hT' hcan' z hz'
  -- the regimes correspond on the prefixes
  have hG : ∀ {Y₀ Z : CMfd.{u} n} (T : BlowupTower Y₁ Y₀) (C : Set Y₀) (π : Z → Y₀) (hπ : IsBlowupAlong n C π),
      IsGeoTestTower (barMarked 𝔍) (P.append (.step T C π hπ)) → IsGeoTestTower (barMarked 𝔍) (P.append T) :=
    fun _ _ _ _ h => h.1
  have hQ : ∀ (s : ℕ) {Y₀ : CMfd.{u} n} (H₀ : BlowupTower Y₁ Y₀) (y : Y₀),
      IsGeoTestTower (barMarked 𝔍) (P.append H₀) →
        (stepRegime 𝔍 s (P.append H₀) y ↔ stepRegime (geoTransformAlong 𝔍 P) s H₀ y) :=
    fun s _ H₀ y hH => (stepRegime_emptyPrefix_iff 𝔍 h𝔍 hd P hP H₀ hH s y).symm
  have hl := level_emptyPrefix 𝔍 P hP T₁ z
  by_cases hs : IsSpecial 𝔍 (P.append T₁) z
  · have hs' := (isSpecial_emptyPrefix_iff 𝔍 h𝔍 hd P hP T₁ hT z).mpr hs
    show stepOneInvL R 𝔍 _ _ z = stepOneInvL R _ _ _ z
    rw [stepOneInvL_of_isSpecial R 𝔍 _ _ hs, stepOneInvL_of_isSpecial R _ _ _ hs', hl]
  · have hs' : ¬ IsSpecial (geoTransformAlong 𝔍 P) T₁ z :=
      fun h => hs ((isSpecial_emptyPrefix_iff 𝔍 h𝔍 hd P hP T₁ hT z).mp h)
    specialize hD hs
    specialize hD' hs'
    show stepOneInvL R 𝔍 _ _ z = stepOneInvL R _ _ _ z
    rw [stepOneInvL_of_not_isSpecial R 𝔍 _ _ hs, stepOneInvL_of_not_isSpecial R _ _ _ hs']
    rw [hl] at hD' ⊢
    obtain ⟨s, hsdef⟩ : ∃ s, level 𝔍 (P.append T₁) z = s := ⟨_, rfl⟩
    have hreg' : stepRegime (geoTransformAlong 𝔍 P) s T₁ z := ⟨hl.trans hsdef, hs'⟩
    rw [hsdef] at hD hD' ⊢
    rcases (regimeRun_le_length (stepRegime (geoTransformAlong 𝔍 P) s) T₁ z).lt_or_eq with hlt | heq
    · -- the run stays inside `T₁`
      have hr := regimeRun_append_of_lt (stepRegime 𝔍 s) (stepRegime (geoTransformAlong 𝔍 P) s) P
        (fun H₀ => IsGeoTestTower (barMarked 𝔍) (P.append H₀)) hG (hQ s) T₁ z hT hlt
      rw [hr] at hD ⊢
      simp only [head, tail] at hD hD' ⊢
      rw [split_append_of_le P T₁ _ hlt.le] at hD ⊢
      dsimp only at hD ⊢
      have hT₀₁ : IsGeoTestTower (barMarked 𝔍) ((P.append (head T₁ (regimeRun (stepRegime (geoTransformAlong 𝔍 P) s) T₁ z))).append
          (tail T₁ (regimeRun (stepRegime (geoTransformAlong 𝔍 P) s) T₁ z))) := by
        rw [BlowupTower.append_assoc, head_append_tail]; exact hT
      have hz₀₁ : z ∈ (geoTransformAlong (barMarked 𝔍) ((P.append (head T₁ (regimeRun (stepRegime (geoTransformAlong 𝔍 P) s) T₁ z))).append
          (tail T₁ (regimeRun (stepRegime (geoTransformAlong 𝔍 P) s) T₁ z)))).cosupp := by
        rw [BlowupTower.append_assoc, head_append_tail]; exact hz
      congr 2
      rcases s with _ | s
      · exact ContactLowerValue.lowerValueL_zero_emptyPrefix R 𝔍 h𝔍 hd P hP _ _ hT₀₁ hz₀₁ hD hD'
      · exact (lowerDataL_succ_emptyPrefix 𝔍 R h𝔍 hd hn P hP _ _ hT₀₁ hD').2
    · -- the run covers `T₁`, then all of `P`
      have hbase := regime_base_of_regimeRun_eq (stepRegime (geoTransformAlong 𝔍 P) s) T₁ z hreg' heq
      have hbaseP : stepRegime 𝔍 s P (T₁.proj z) := (hQ s .refl (T₁.proj z) hPJ).mpr hbase
      have hstep : ∀ {Y' Z' : CMfd.{u} n} (T : BlowupTower X Y') (π : Z' → Y') (hπ : IsBlowupAlong n (∅ : Set Y') π),
          IsEmptyTower T → ∀ w : Z', stepRegime 𝔍 s (.step T ∅ π hπ) w → stepRegime 𝔍 s T (π w) := by
        intro Y' Z' T π hπ hTe w hw
        have hTt : IsGeoTestTower (barMarked 𝔍) T := isGeoTestTower_of_isEmptyTower _ T hTe
        have hl' := level_step_of_notMem 𝔍 hE T ∅ π hπ (notMem_empty (π w))
        have hs'' := isSpecial_step_iff_of_notMem 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hE T hTt ∅ π hπ
          (notMem_empty (π w))
        exact ⟨hl'.symm.trans hw.1, fun h => hw.2 (hs''.mpr h)⟩
      have hrP := regimeRun_eq_length_of_isEmptyTower (stepRegime 𝔍 s) hstep P hP _ hbaseP
      have hr := regimeRun_append_of_eq (stepRegime 𝔍 s) (stepRegime (geoTransformAlong 𝔍 P) s) P
        (fun H₀ => IsGeoTestTower (barMarked 𝔍) (P.append H₀)) hG (hQ s) T₁ z hT heq
      rw [hr, hrP] at hD ⊢
      rw [heq] at hD' ⊢
      simp only [head, tail] at hD hD' ⊢
      rw [split_of_length_le (P.append T₁) _ (by rw [BlowupTower.length_append]; omega)] at hD ⊢
      rw [split_of_length_le T₁ _ le_rfl] at hD' ⊢
      dsimp only at hD hD' ⊢
      congr 2
      rcases s with _ | s
      · have h := ContactLowerValue.lowerValueL_zero_emptyPrefix_rebase R 𝔍 h𝔍 hd .refl P
          (by rw [BlowupTower.refl_append]; exact hP) T₁ (by rw [BlowupTower.refl_append]; exact hT)
          (by rw [BlowupTower.refl_append]; exact hz) hD (by rw [BlowupTower.refl_append]; exact hD')
        rw [BlowupTower.refl_append] at h
        exact h
      · exact lowerValueL_succ_emptyPrefix_refl 𝔍 R h𝔍 hd hn P hP T₁ hT hD hD'

/-- **Property (4') of the masked Step 1 value function** (`hir:step-one-empty-prefix`; the field `emptyPrefix` of
`ResolutionInvariantExt.ResolutionInvariant`): for `𝔍` well formed with `d ≥ 1`, of maximal order along `N` with `dim N ≤ k`
(`0 < n`), `R` a resolution invariant in dimension `≤ k - 1`, `P` a tower with only empty centres and `P T₁` a canonical
segment of `stepOneInvM R 𝔍`, the tower `T₁` is a canonical segment of `stepOneInvM R 𝔍_P` and, at every point of the cosupport
of `J̄_{P T₁}`, the value of `𝔍` along `P T₁` is that of `𝔍_P` along `T₁` (induction on `T₁`: the maximum loci agree, the
cosupports being equal, `restrictEquiv_barMarked_append`). -/
theorem stepOneInvM_emptyPrefix (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y₁ : CMfd.{u} n} (P : BlowupTower X Y₁)
    (hP : IsEmptyTower P) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₁ Y), IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) (P.append T₁) →
      IsCanonical (barMarked (geoTransformAlong 𝔍 P)) (stepOneInvM R (geoTransformAlong 𝔍 P)) T₁ ∧
        ∀ z ∈ (geoTransformAlong (barMarked 𝔍) (P.append T₁)).cosupp,
          stepOneInvM R 𝔍 (P.append T₁) z = stepOneInvM R (geoTransformAlong 𝔍 P) T₁ z
  | _, .refl, hcan => ⟨trivial, fun _ hz => stepOneInvM_emptyPrefix_eq 𝔍 R h𝔍 hd hn hmax hk P hP .refl hcan trivial hz⟩
  | _, .step T C π hπ, hcan => by
      have hcan₀ := hcan
      obtain ⟨hcanT, hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) (P.append T) ∧
          (C = ∅ ∨ C = maxLocus (stepOneInvM R 𝔍 (P.append T)) (geoTransformAlong (barMarked 𝔍) (P.append T)).cosupp) :=
        hcan
      obtain ⟨hcan'T, hval⟩ := stepOneInvM_emptyPrefix h𝔍 hd hn hmax hk P hP T hcanT
      have hT := StepOneAdmissible.isGeoTestTower_of_isCanonical_stepOneInvM 𝔍 R h𝔍 hd hn hmax hk _ hcanT
      have hEqT := restrictEquiv_barMarked_append 𝔍 h𝔍 hd P hP T hT
      have hcan'S : IsCanonical (barMarked (geoTransformAlong 𝔍 P)) (stepOneInvM R (geoTransformAlong 𝔍 P))
          (.step T C π hπ) := by
        refine (⟨hcan'T, hC.imp id fun h => h.trans ?_⟩ :
          IsCanonical (barMarked (geoTransformAlong 𝔍 P)) (stepOneInvM R (geoTransformAlong 𝔍 P)) T ∧
            (C = ∅ ∨ C = maxLocus (stepOneInvM R (geoTransformAlong 𝔍 P) T)
              (geoTransformAlong (barMarked (geoTransformAlong 𝔍 P)) T).cosupp))
        rw [hEqT.cosupp_eq]
        exact ResolutionInvariantExt.maxLocus_congr hval
      exact ⟨hcan'S, fun _ hz => stepOneInvM_emptyPrefix_eq 𝔍 R h𝔍 hd hn hmax hk P hP _ hcan₀ hcan'S hz⟩

end EmptyPrefix

end

end Hironaka.StepOneEmptyPrefix
