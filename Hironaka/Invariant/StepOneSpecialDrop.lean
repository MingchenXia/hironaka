/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneCanonicalTail
import Hironaka.MarkedIdeal.CodimOneCentreAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.BoundaryCount
import Hironaka.Invariant.BoundaryCountAlong
import Hironaka.MarkedIdeal.CodimOneSupport
import Hironaka.MarkedIdeal.CodimOneSupportAlong
import Hironaka.Invariant.ContactIndependenceAlong
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Blowup.NormalCrossings
import Hironaka.Blowup.NormalCrossingsComparison
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.Invariant.StepOneMaskTower
import Hironaka.Invariant.StepOneRegime
import Hironaka.Invariant.StepOneValue
import Hironaka.Invariant.StepOneValueMasked
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1: the value drops over the special points of a canonical centre

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`: Step 1aa ("the intersections `H^s_α ∩
N` contained in the support ... blowing them up decreases `s`") and Step 1ba ("blowing up the codimension one
components ... removes them from the support").

Property (3) of the Step 1 value function (`hir:centre-function`, "the value drops over the centre") at the **special** points,
for every family of lower marked ideals (`StepOneValueMasked.stepOneInvL`).  Let `T σ` be a multiple test blow-up of
`J̄ = 𝓒_N(𝓗_N(𝔍))` whose last centre `C` is the maximum locus of the Step 1 value at the last stage of `T`, and `x ∈ C` a special
point of level `s`, so the maximum is `(s, ∞)`:

* `s ≥ 1` (Step 1aa): near `x`, the points of `N` on the original members through `x` lie in the cosupport (the
  member locus), have level `s` and are special, hence have the maximal value and lie in `C`;
  `BoundaryCountAlong.boundaryCount_map_geoStrictTransform_lt_boundaryCount_along` then makes the level drop at
  every point of the cosupport over `x` (`level_step_lt_of_isSpecial`);
* `s = 0` (Step 1ba): near `x` the cosupport is the codimension-one part `Z₁` (every point of it there has level `0`
  and is special, so lies in `C`), so `C` is regular of codimension one in `N` at `x`, and by maximal order
  `CodimOneCentreAlong.notMem_cosupp_geoTransform_of_codim_one_along` leaves no point of the cosupport over `x`
  (`notMem_cosupp_step_of_isSpecial_zero`).

Hence `stepOneInvL_step_lt_of_isSpecial`: at every point of the cosupport over a special point of the centre the value drops.
No lower data are needed.  With the canonical-tail theorem (`StepOneCanonicalTail`) this completes **property (3)** of the
masked Step 1 value function along canonical segments which are multiple test blow-ups (`stepOneInvM_decrease`, the form of
the field `decrease` of `ResolutionInvariantExt.ResolutionInvariant`): blowing up the nonempty maximum locus, the value drops over
it and is unchanged off it.  Likewise **property (4)** (`stepOneInvM_emptyStep`, the field `emptyStep`): a blowup along
the empty centre does not change the values.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneSpecialDrop

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneValue Hironaka.StepOneLowerDomain Hironaka.StepOneValueMasked Hironaka.BoundaryCount Hironaka.CodimOneSupportAlong Hironaka.MemberInterLocusAlong Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen Hironaka.HomogenizedIdealAlong Hironaka.BlowupStrictSubmanifold Hironaka.GermIdealOrder Hironaka.NormalCrossings
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)

noncomputable section

variable {n : ℕ}

section Drop

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)
  (𝔍 : MarkedIdeal n X) (L : LowerFamily 𝔍)

/-- **On the maximum locus with a special point of level `s`, every point of the cosupport has level at most `s`.** -/
theorem level_le_of_mem_maxLocus {Y : CMfd.{u} n} (T : BlowupTower X Y) {x : Y}
    (hx : x ∈ maxLocus (stepOneInvL R 𝔍 L T) (geoTransformAlong (barMarked 𝔍) T).cosupp) (hsp : IsSpecial 𝔍 T x)
    {y : Y} (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) : level 𝔍 T y ≤ level 𝔍 T x := by
  have h := hx.2 y hy
  rw [stepOneInvL_of_isSpecial R 𝔍 L T hsp, Prod.Lex.le_iff, stepOneInvL_fst] at h
  simp only [ofLex_toLex] at h
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-- **A special point of the level of a special point of the maximum locus lies in it** (it has the maximal value
`(s, ∞)`). -/
theorem mem_maxLocus_of_isSpecial {Y : CMfd.{u} n} (T : BlowupTower X Y) {x : Y}
    (hx : x ∈ maxLocus (stepOneInvL R 𝔍 L T) (geoTransformAlong (barMarked 𝔍) T).cosupp) (hsp : IsSpecial 𝔍 T x)
    {y : Y} (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) (hysp : IsSpecial 𝔍 T y)
    (hl : level 𝔍 T y = level 𝔍 T x) :
    y ∈ maxLocus (stepOneInvL R 𝔍 L T) (geoTransformAlong (barMarked 𝔍) T).cosupp := by
  have heq : stepOneInvL R 𝔍 L T y = stepOneInvL R 𝔍 L T x := by
    rw [stepOneInvL_of_isSpecial R 𝔍 L T hysp, stepOneInvL_of_isSpecial R 𝔍 L T hsp, hl]
  exact ⟨hy, fun y' hy' => (hx.2 y' hy').trans_eq heq.symm⟩

/-- **Step 1ba: over a special point of level `0` of the centre there is no point of the cosupport** (`𝔍` well formed, `d ≥ 1`,
of maximal order; the centre the maximum locus of the Step 1 value along a multiple test blow-up `T σ` of `J̄`). -/
theorem notMem_cosupp_step_of_isSpecial_zero (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (hT : IsGeoTestTower (barMarked 𝔍) (.step T C π hπ))
    (hC : C = maxLocus (stepOneInvL R 𝔍 L T) (geoTransformAlong (barMarked 𝔍) T).cosupp) {z : Z} (hzC : π z ∈ C)
    (hl0 : level 𝔍 T (π z) = 0) (hsp : IsSpecial 𝔍 T (π z)) :
    z ∉ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp := by
  obtain ⟨hTT, hCadm⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T hTT
  have hmaxT := isMaximalOrderAlong_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent
    (isMaximalOrderAlong_barMarked 𝔍 h𝔍 hd hmax) T hTT
  have hdT : 1 ≤ (geoTransformAlong (barMarked 𝔍) T).d := by
    rw [d_geoTransformAlong]; exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hsub : C ⊆ (geoTransformAlong (barMarked 𝔍) T).cosupp := hCadm.2.1
  have hxmax : π z ∈ maxLocus (stepOneInvL R 𝔍 L T) (geoTransformAlong (barMarked 𝔍) T).cosupp := hC ▸ hzC
  have hZ : π z ∈ codimOnePartAlong (geoTransformAlong (barMarked 𝔍) T).N (geoTransformAlong (barMarked 𝔍) T).ideal
      (geoTransformAlong (barMarked 𝔍) T).d := by
    rcases hsp with ⟨-, hZ⟩ | ⟨h1, -⟩
    · exact hZ
    · omega
  obtain ⟨k', hNk, hSk⟩ := hZ
  -- near `π z` the cosupport is `Z₁`, all of whose points are special of level `0`, hence in `C`
  have hev : ∀ᶠ y in 𝓝 (π z), y ∈ cosupport n (geoTransformAlong (barMarked 𝔍) T).N
      (geoTransformAlong (barMarked 𝔍) T).ideal (geoTransformAlong (barMarked 𝔍) T).d ↔ y ∈ C := by
    filter_upwards [eventually_mem_codimOnePartAlong_iff ⟨k', hNk, hSk⟩] with y hy
    constructor
    · intro hyc
      have hyl : level 𝔍 T y = 0 := Nat.eq_zero_of_le_zero
        ((level_le_of_mem_maxLocus R 𝔍 L T hxmax hsp hyc).trans_eq hl0)
      have hysp : IsSpecial 𝔍 T y := Or.inl ⟨hyl, hy.mpr hyc⟩
      rw [hC]
      exact mem_maxLocus_of_isSpecial R 𝔍 L T hxmax hsp hyc hysp (hyl.trans hl0.symm)
    · exact fun hyC => hsub hyC
  have hCk := CodimOneSupport.regularAtDim_of_eventually_mem_iff hev hSk
  exact CodimOneCentreAlong.notMem_cosupp_geoTransform_of_codim_one_along hπ hNT hcT hdT hsub hzC hCk hNk
    (hmaxT (π z))

open Classical in
/-- **Step 1aa: over a special point of level `s ≥ 1` of the centre the level drops** (`𝔍` well formed; the centre the maximum
locus of the Step 1 value along a multiple test blow-up `T σ` of `J̄`): at every point `z` of the cosupport over it,
`s(z) < s(σ z)`. -/
theorem level_step_lt_of_isSpecial (h𝔍 : 𝔍.IsWellFormed) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y)
    (π : Z → Y) (hπ : IsBlowupAlong n C π) (hT : IsGeoTestTower (barMarked 𝔍) (.step T C π hπ))
    (hC : C = maxLocus (stepOneInvL R 𝔍 L T) (geoTransformAlong (barMarked 𝔍) T).cosupp) {z : Z}
    (hz : z ∈ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp) (hzC : π z ∈ C)
    (hl1 : 1 ≤ level 𝔍 T (π z)) (hsp : IsSpecial 𝔍 T (π z)) :
    level 𝔍 (.step T C π hπ) z < level 𝔍 T (π z) := by
  obtain ⟨hTT, hCadm⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T hTT
  set E := origMembers 𝔍 T with hEdef
  have hEsub : ∀ H ∈ E, H ∈ (geoTransformAlong (barMarked 𝔍) T).E := fun H hH => List.mem_of_mem_take hH
  have hE : IsSNCDivisor n E := NormalCrossingsComparison.isSNCDivisor_of_sublist hwf.isSNCDivisor (List.take_sublist _ _)
  have hTr : IsTransverse n (geoTransformAlong (barMarked 𝔍) T).N E :=
    NormalCrossingsComparison.isTransverse_of_forall_mem hwf.isTransverse hEsub
  have hnc : HasNormalCrossings n C E := NormalCrossingsComparison.hasNormalCrossings_of_forall_mem hCadm.2.2 hEsub
  have hsub : C ⊆ (geoTransformAlong (barMarked 𝔍) T).cosupp := hCadm.2.1
  have hCN : C ⊆ (geoTransformAlong (barMarked 𝔍) T).N := hsub.trans (MarkedIdeal.cosupp_subset_N _)
  have hzN : z ∈ geoStrictTransform π C (geoTransformAlong (barMarked 𝔍) T).N :=
    (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp_subset_N hz
  have hxmax : π z ∈ maxLocus (stepOneInvL R 𝔍 L T) (geoTransformAlong (barMarked 𝔍) T).cosupp := hC ▸ hzC
  have hL : π z ∈ memberInterLocus (geoTransformAlong (barMarked 𝔍) T).N E
      (geoTransformAlong (barMarked 𝔍) T).cosupp := by
    rcases hsp with ⟨h0, -⟩ | ⟨-, hL⟩
    · omega
    · exact hL
  -- near `π z`, the points of `N` on the original members through `π z` lie in `C`
  have hC' : ∀ᶠ y in 𝓝 (π z), y ∈ (geoTransformAlong (barMarked 𝔍) T).N →
      (∀ i : Fin E.length, π z ∈ E.get i → y ∈ E.get i) → y ∈ C := by
    filter_upwards [hL.2, hL.2.eventually_nhds] with y hy1 hy2 hyN hyall
    have hyc := hy1 hyN hyall
    have hge : level 𝔍 T (π z) ≤ level 𝔍 T y := by
      show (Finset.univ.filter fun i : Fin E.length => π z ∈ E.get i).card ≤
        (Finset.univ.filter fun i : Fin E.length => y ∈ E.get i).card
      refine Finset.card_le_card fun i hi => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hyall i hi
    have hle := level_le_of_mem_maxLocus R 𝔍 L T hxmax hsp hyc
    have hysp : IsSpecial 𝔍 T y := Or.inr ⟨hl1.trans hge, hyc,
      hy2.mono fun y' hy' hy'N hy'all => hy' hy'N fun i hi => hy'all i (hyall i hi)⟩
    rw [hC]
    exact mem_maxLocus_of_isSpecial R 𝔍 L T hxmax hsp hyc hysp (le_antisymm hle hge)
  have hlt := BoundaryCountAlong.boundaryCount_map_geoStrictTransform_lt_boundaryCount_along hπ hCN hE hTr hnc hzC hzN hC'
  have hlev : level 𝔍 (.step T C π hπ) z = boundaryCount (E.map (geoStrictTransform π C)) z := by
    have hlen : (barMarked 𝔍).E.length ≤
        ((geoTransformAlong (barMarked 𝔍) T).E.map (geoStrictTransform π C)).length := by
      rw [List.length_map, MarkedIdeal.length_E_geoTransformAlong]; omega
    show boundaryCount ((geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).E.take (barMarked 𝔍).E.length) z = _
    rw [MarkedIdeal.geoTransformAlong_step, MarkedIdeal.geoTransform_E, List.take_append_of_le_length hlen,
      ← List.map_take]
    rfl
  rw [hlev]
  exact hlt

/-- **Property (3) of the Step 1 value function at special points: the value drops over a special point of the centre**
(for every family of lower marked ideals; `𝔍` well formed, `d ≥ 1`, of maximal order): along a multiple test blow-up `T σ` of
`J̄` whose last centre `C` is the maximum locus of `stepOneInvL R 𝔍 L` at the last stage of `T`, at every point `z` of the
cosupport over a special point of `C` the value drops. -/
theorem stepOneInvL_step_lt_of_isSpecial (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (hT : IsGeoTestTower (barMarked 𝔍) (.step T C π hπ))
    (hC : C = maxLocus (stepOneInvL R 𝔍 L T) (geoTransformAlong (barMarked 𝔍) T).cosupp) {z : Z}
    (hz : z ∈ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp) (hzC : π z ∈ C)
    (hsp : IsSpecial 𝔍 T (π z)) :
    stepOneInvL R 𝔍 L (.step T C π hπ) z < stepOneInvL R 𝔍 L T (π z) := by
  rcases Nat.eq_zero_or_pos (level 𝔍 T (π z)) with h0 | hpos
  · exact absurd hz (notMem_cosupp_step_of_isSpecial_zero R 𝔍 L h𝔍 hd hmax T C π hπ hT hC hzC h0 hsp)
  · exact stepOneInvL_lt_of_level_lt R 𝔍 L (level_step_lt_of_isSpecial R 𝔍 L h𝔍 T C π hπ hT hC hz hzC hpos hsp)

end Drop

/-! ### Property (3) of the masked Step 1 value function -/

section Decrease

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n (k - 1) Λ)
  (𝔍 : MarkedIdeal n X)

open StepOneRegime StepOneMaskTower StepOneCanonicalTail in
/-- **Property (3) of the masked Step 1 value function** (`hir:step-one-special-drop`; the field `decrease` of
`ResolutionInvariantExt.ResolutionInvariant` for `stepOneInvM`, along multiple test blow-ups): let `𝔍` be well formed with
`d ≥ 1`, of maximal order along `N` with `dim N ≤ k` (`0 < n`), `R` a resolution invariant in dimension `≤ k - 1`, `T` a canonical
segment of `stepOneInvM R 𝔍` and `C` the maximum locus of `stepOneInvM R 𝔍 T` on the cosupport (nonemptiness is not needed),
with `T σ` (`σ` the blowup along `C`) a multiple test blow-up of `J̄` (this hypothesis is what property (1) will supply).
At every point `z` of the cosupport after `σ`, the value drops if `σ z ∈ C` and is unchanged otherwise.  (Special points: `stepOneInvL_step_lt_of_isSpecial`; non-special points: a smaller level, or the same
level, then `z` is not special (it lies over the mask of `σ z`) and the canonical-tail theorem applies.) -/
theorem stepOneInvM_decrease (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : ResolutionInvariantSpec.DimLE n 𝔍.N k) {Y Z : CMfd.{u} n}
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower (barMarked 𝔍) (.step T C π hπ))
    (hcan : ResolutionInvariantSpec.IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T)
    (hC : C = maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp) :
    ∀ z ∈ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp,
      (π z ∈ C → stepOneInvM R 𝔍 (.step T C π hπ) z < stepOneInvM R 𝔍 T (π z)) ∧
      (π z ∉ C → stepOneInvM R 𝔍 (.step T C π hπ) z = stepOneInvM R 𝔍 T (π z)) := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  have hcanS : ResolutionInvariantSpec.IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) (.step T C π hπ) :=
    ⟨hcan, Or.inr hC⟩
  intro z hz
  refine ⟨fun hzC => ?_, fun hzC =>
    stepOneInvM_step_of_notMem_of_isCanonical 𝔍 R h𝔍 hd hn hmax hk T C π hπ hT hcanS hz hzC⟩
  by_cases hsp : IsSpecial 𝔍 T (π z)
  · exact stepOneInvL_step_lt_of_isSpecial R 𝔍 (lowerMarkedM 𝔍) h𝔍 hd hmax T C π hπ hT hC hz hzC hsp
  · rcases (level_step_le 𝔍 hE T C π hπ z).lt_or_eq with hlt | heq
    · exact stepOneInvL_lt_of_level_lt R 𝔍 _ hlt
    · obtain ⟨hTT, hCadm⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
      have hJ := isWellFormed_barMarked 𝔍 h𝔍
      obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N
        hJ.isCoherent T hTT
      have hzc : π z ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp :=
        proj_mem_cosupp_of_mem_cosupp (𝔪 := geoTransformAlong (barMarked 𝔍) T) hNT hcT (.step .refl C π hπ)
          ⟨trivial, hCadm⟩ hz
      have hreg : stepRegime 𝔍 (level 𝔍 T (π z)) T (π z) := ⟨rfl, hsp⟩
      have hmask := mem_lowerMask_of_stepRegime 𝔍 h𝔍 hd hn hmax T hTT hzc hreg
      have hzs : ¬ IsSpecial 𝔍 (.step T C π hπ) z :=
        (stepRegime_and_le_regimeRun_of_mem_lowerMask 𝔍 h𝔍 hd hmax T (.step .refl C π hπ) hT rfl hmask heq).1.2
      exact stepOneInvM_step_lt_of_mem_of_isCanonical 𝔍 R h𝔍 hd hn hmax hk T C π hπ hT hcanS hz hzC hzs hsp heq

open StepOneCanonicalTail in
/-- **Property (4) of the masked Step 1 value function** (`hir:step-one-special-drop`; the field `emptyStep` of
`ResolutionInvariantExt.ResolutionInvariant` for `stepOneInvM`): after a canonical segment `T` of `stepOneInvM R 𝔍` which is a
multiple test blow-up of `J̄`, a blowup along the empty centre does not change the values. -/
theorem stepOneInvM_emptyStep (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : ResolutionInvariantSpec.DimLE n 𝔍.N k) {Y Z : CMfd.{u} n}
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) (hC : C = ∅)
    (hT : IsGeoTestTower (barMarked 𝔍) T)
    (hcan : ResolutionInvariantSpec.IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T) :
    ∀ z ∈ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp,
      stepOneInvM R 𝔍 (.step T C π hπ) z = stepOneInvM R 𝔍 T (π z) := by
  subst hC
  have hTS : IsGeoTestTower (barMarked 𝔍) (.step T ∅ π hπ) :=
    (isGeoTestTower_step_iff _ T ∅ π hπ).mpr ⟨hT, MarkedIdeal.isAdmissibleCentre_empty _⟩
  intro z hz
  exact stepOneInvM_step_of_notMem_of_isCanonical 𝔍 R h𝔍 hd hn hmax hk T ∅ π hπ hTS ⟨hcan, Or.inl rfl⟩ hz
    (Set.notMem_empty _)

end Decrease

end

end Hironaka.StepOneSpecialDrop
