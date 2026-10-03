/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneValueMasked
import Hironaka.Invariant.CodimOneAdmissibleAlong
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Invariant.CodimOnePartCanonical
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.BoundaryCount
import Hironaka.MarkedIdeal.CodimOneSupportAlong
import Hironaka.Invariant.ContactIndependenceAlong
import Hironaka.Invariant.ContactStageInvDomain
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Blowup.NormalCrossingsInvariance
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.Invariant.StepOneRegime
import Hironaka.Invariant.StepOneValue
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1: admissibility of the top level sets of the value

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`: Step 1aa ("the intersections `H^s_α ∩
N` contained in the support ... are disjoint ... we blow them up") and Step 1ba ("the codimension one components of
the support ... blow them up").

Property (1) of the Step 1 value function (`hir:centre-function`, "admissibility of the level sets of the maximum, on open
sets") at the **top values** `(s, ∞)`, for every family of lower marked ideals (`StepOneValueMasked.stepOneInvL`).  Along a
multiple test blow-up `T` of `J̄ = 𝓒_N(𝓗_N(𝔍))`, the points of the cosupport with value `(s, ∞)` are exactly the special
points of level `s` (`stepOneInvL_eq_top_iff`: a lower value is never `∞`).  On an open `W` of the last stage on which the
value is `≤ (s, ∞)` on the cosupport (i.e. the level is `≤ s`):

* `s ≥ 1` (Step 1aa): the special points of level `s` in `W` are the level-`s` part of the member locus of the
  restriction to `W`, an admissible centre by `MemberInterLocusAlong.isAdmissibleCentre_memberInterLocus_level`
  (`isAdmissibleCentre_top_of_one_le`);
* `s = 0` (Step 1ba): the special points in `W` are the trace on `W` of the codimension-one part `Z₁` of the
  cosupport, a closed submanifold (`CodimOneSupportAlong.isClosedSubmanifold_codimOnePartAlong`, maximal order)
  transverse to the exceptional members (`CodimOneAdmissibleAlong.isTransverse_codimOnePartAlong_drop_E`), and over
  `W` the cosupport misses the original members (`isAdmissibleCentre_top_zero`;
  `ContactStageInvDomain.isTransverse_append_of_forall_notMem`).

Hence `stepOneInvL_admissible_top`: the shape of the field `admissible` of `ResolutionInvariantExt.ResolutionInvariant` at
the values `(s, ∞)`.  (The values `(s, λ)` with `λ < ∞` -- the non-special level sets, from the admissibility of the lower
invariant on the masks -- are not treated here.)
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneAdmissibleTop

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneValue Hironaka.StepOneLowerDomain Hironaka.StepOneValueMasked Hironaka.BoundaryCount Hironaka.CodimOneSupportAlong Hironaka.MemberInterLocusAlong Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen Hironaka.HomogenizedIdealAlong Hironaka.BlowupStrictSubmanifold Hironaka.GermIdealOrder Hironaka.NormalCrossings Hironaka.NormalCrossingsInvariance Hironaka.BlowupRestrictOpen
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)

noncomputable section

variable {n : ℕ}

open Classical in
/-- A point on a member of `E` is counted: `s(y) ≥ 1`. -/
theorem one_le_boundaryCount_of_mem {M : Type*} [TopologicalSpace M] {E : List (Set M)} {H : Set M} (hH : H ∈ E)
    {y : M} (hy : y ∈ H) : 1 ≤ boundaryCount E y := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
  unfold boundaryCount
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩⟩

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)
  (𝔍 : MarkedIdeal n X) (L : LowerFamily 𝔍)

/-- **A value `≤ (s, ∞)` has level `≤ s`.** -/
theorem level_le_of_stepOneInvL_le {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y} {s : ℕ}
    (h : stepOneInvL R 𝔍 L T y ≤ toLex (s, (⊤ : WithTop Λ))) : level 𝔍 T y ≤ s := by
  rw [Prod.Lex.le_iff, stepOneInvL_fst] at h
  simp only [ofLex_toLex] at h
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-- **The top values are the special points**: along a multiple test blow-up of `J̄` (`𝔍` well formed, `d ≥ 1`, of maximal
order, `0 < n`), a point of the cosupport has the value `(s, ∞)` iff it is special of level `s` (a lower value is never
`∞`, `StepOneValueMasked.lowerValueL_ne_top`). -/
theorem stepOneInvL_eq_top_iff (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) {y : Y} (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) (s : ℕ) :
    stepOneInvL R 𝔍 L T y = toLex (s, (⊤ : WithTop Λ)) ↔ IsSpecial 𝔍 T y ∧ level 𝔍 T y = s := by
  by_cases hsp : IsSpecial 𝔍 T y
  · rw [stepOneInvL_of_isSpecial R 𝔍 L T hsp]
    constructor
    · intro h
      exact ⟨hsp, congrArg (fun p => (ofLex p).1) h⟩
    · rintro ⟨-, h⟩
      rw [h]
  · rw [stepOneInvL_of_not_isSpecial R 𝔍 L T hsp]
    refine ⟨fun h => ?_, fun h => absurd h.1 hsp⟩
    exact absurd (congrArg (fun p => (ofLex p).2) h) (lowerValueL_ne_top 𝔍 R h𝔍 hd hn hmax L T hT hy hsp)

/-- **Step 1aa: on an open set where the level is `≤ s` (`s ≥ 1`), the points of value `(s, ∞)` form an admissible
centre** of the restriction to `W` of the transform of `J̄` along a multiple test blow-up `T`: they are the
level-`s` part of the member locus of the cosupport along the original members
(`MemberInterLocusAlong.isAdmissibleCentre_memberInterLocus_level` on the restriction). -/
theorem isAdmissibleCentre_top_of_one_le (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (W : Opens Y) {s : ℕ} (hs : 1 ≤ s)
    (hle : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W → level 𝔍 T y ≤ s) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        stepOneInvL R 𝔍 L T y = toLex (s, (⊤ : WithTop Λ))}) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T hT
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T hT
  have hc := cosupp_pullback_val (geoTransformAlong (barMarked 𝔍) T)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) W
  have hwfW := IsWellFormed.pullback_val hwf W
  have hsub : ((origMembers 𝔍 T).map ((Subtype.val : W → Y) ⁻¹' ·)).Sublist
      (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).E :=
    (List.take_sublist _ _).map _
  have hbound : ∀ x ∈ (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).cosupp,
      boundaryCount ((origMembers 𝔍 T).map ((Subtype.val : W → Y) ⁻¹' ·)) x ≤ s := by
    intro x hx
    rw [hc] at hx
    rw [CodimOnePartCanonical.boundaryCount_map_preimage]
    exact hle _ hx x.2
  have hdW : 1 ≤ (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).d := by
    show 1 ≤ (geoTransformAlong (barMarked 𝔍) T).d
    rw [d_geoTransformAlong]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hadm := isAdmissibleCentre_memberInterLocus_level _ hwfW hdW hn hsub s hbound
  convert hadm using 1
  ext p
  have hmem : p ∈ memberInterLocus (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).N
      ((origMembers 𝔍 T).map ((Subtype.val : W → Y) ⁻¹' ·))
      (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).cosupp ↔
      (p : Y) ∈ memberInterLocus (geoTransformAlong (barMarked 𝔍) T).N (origMembers 𝔍 T)
        (geoTransformAlong (barMarked 𝔍) T).cosupp := by
    rw [hc]
    exact mem_memberInterLocus_preimage_iff Subtype.val (W.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq p) _ _ _
  have hcount : boundaryCount ((origMembers 𝔍 T).map ((Subtype.val : W → Y) ⁻¹' ·)) p = level 𝔍 T p :=
    CodimOnePartCanonical.boundaryCount_map_preimage _ _ _
  simp only [mem_preimage, mem_ofPred_eq, mem_inter_iff]
  rw [hmem, hcount]
  constructor
  · rintro ⟨hy, hv⟩
    obtain ⟨hsp, hl⟩ := (stepOneInvL_eq_top_iff R 𝔍 L h𝔍 hd hn hmax T hT hy s).mp hv
    rcases hsp with ⟨h0, -⟩ | ⟨-, hL⟩
    · omega
    · exact ⟨hL, hl⟩
  · rintro ⟨hL, hl⟩
    have hy : (p : Y) ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp := (mem_memberInterLocus_iff.mp hL).1
    exact ⟨hy, (stepOneInvL_eq_top_iff R 𝔍 L h𝔍 hd hn hmax T hT hy s).mpr ⟨Or.inr ⟨hs.trans_eq hl.symm, hL⟩, hl⟩⟩

/-- **Step 1ba: on an open set where the level is `0`, the points of value `(0, ∞)` form an admissible centre** of the
restriction to `W` of the transform of `J̄` along a multiple test blow-up `T`: they are the trace on `W` of the
codimension-one part of the cosupport, a closed submanifold (maximal order) transverse to the exceptional members,
and over `W` the cosupport misses the original members. -/
theorem isAdmissibleCentre_top_zero (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (W : Opens Y)
    (hle : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W → level 𝔍 T y ≤ 0) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        stepOneInvL R 𝔍 L T y = toLex (0, (⊤ : WithTop Λ))}) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hmaxJ := isMaximalOrderAlong_barMarked 𝔍 h𝔍 hd hmax
  have hdJ : 1 ≤ (barMarked 𝔍).d := ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T hT
  have hmaxT := isMaximalOrderAlong_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent hmaxJ T hT
  have hdT : 1 ≤ (geoTransformAlong (barMarked 𝔍) T).d := by rw [d_geoTransformAlong]; exact hdJ
  have hc := cosupp_pullback_val (geoTransformAlong (barMarked 𝔍) T)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) W
  have hset : (Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        stepOneInvL R 𝔍 L T y = toLex (0, (⊤ : WithTop Λ))} =
      (Subtype.val : W → Y) ⁻¹' codimOnePartAlong (geoTransformAlong (barMarked 𝔍) T).N
        (geoTransformAlong (barMarked 𝔍) T).ideal (geoTransformAlong (barMarked 𝔍) T).d := by
    ext p
    simp only [mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨hy, hv⟩
      obtain ⟨hsp, -⟩ := (stepOneInvL_eq_top_iff R 𝔍 L h𝔍 hd hn hmax T hT hy 0).mp hv
      rcases hsp with ⟨-, hZ⟩ | ⟨h1, hL⟩
      · exact hZ
      · have := hle _ hy p.2
        omega
    · intro hZ
      have hy : (p : Y) ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp := codimOnePartAlong_subset hZ
      have hl : level 𝔍 T p = 0 := Nat.eq_zero_of_le_zero (hle _ hy p.2)
      exact ⟨hy, (stepOneInvL_eq_top_iff R 𝔍 L h𝔍 hd hn hmax T hT hy 0).mpr ⟨Or.inl ⟨hl, hZ⟩, hl⟩⟩
  rw [hset]
  refine ⟨isClosedSubmanifold_preimage_val (isClosedSubmanifold_codimOnePartAlong hcT hNT hdT hmaxT) W, ?_, ?_⟩
  · rw [hc]
    exact preimage_mono codimOnePartAlong_subset
  · have htr := CodimOneAdmissibleAlong.isTransverse_codimOnePartAlong_drop_E (barMarked 𝔍) hJ hdJ hmaxJ T hT
    have htrW := isTransverse_preimage (pullsBackCoordinates_val W) htr
    have hE : (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).E =
        (origMembers 𝔍 T).map ((Subtype.val : W → Y) ⁻¹' ·) ++
          ((geoTransformAlong (barMarked 𝔍) T).E.drop (barMarked 𝔍).E.length).map ((Subtype.val : W → Y) ⁻¹' ·) := by
      show (geoTransformAlong (barMarked 𝔍) T).E.map _ =
        ((geoTransformAlong (barMarked 𝔍) T).E.take (barMarked 𝔍).E.length).map _ ++ _
      rw [← List.map_append, List.take_append_drop]
    rw [hE]
    refine (ContactStageInvDomain.isTransverse_append_of_forall_notMem htrW ?_).hasNormalCrossings
    intro H hH x hx hxH
    obtain ⟨H', hH', rfl⟩ := List.mem_map.mp hH
    have hy : (x : Y) ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp := codimOnePartAlong_subset hx
    have h0 := hle _ hy x.2
    have h1 : 1 ≤ level 𝔍 T x := one_le_boundaryCount_of_mem hH' hxH
    omega

/-- **Property (1) of the Step 1 value function at the top values** (`hir:step-one-admissible-top`; the field `admissible` of
`ResolutionInvariantExt.ResolutionInvariant` at the values `(s, ∞)`, for every family of lower marked ideals): let `𝔍` be well
formed with `d ≥ 1`, of maximal order along `N`, `0 < n`, `T` a multiple test blow-up of `J̄` and `W` an open of its last stage
on which the value is `≤ (s, ∞)` on the cosupport.  Then the points of `W` in the cosupport with value `(s, ∞)` form an
admissible centre of the restriction to `W` of the transform. -/
theorem stepOneInvL_admissible_top (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (W : Opens Y) (s : ℕ)
    (hle : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W →
      stepOneInvL R 𝔍 L T y ≤ toLex (s, (⊤ : WithTop Λ))) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        stepOneInvL R 𝔍 L T y = toLex (s, (⊤ : WithTop Λ))}) := by
  have hlev : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W → level 𝔍 T y ≤ s :=
    fun y hy hyW => level_le_of_stepOneInvL_le R 𝔍 L T (hle y hy hyW)
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · exact isAdmissibleCentre_top_zero R 𝔍 L h𝔍 hd hn hmax T hT W hlev
  · exact isAdmissibleCentre_top_of_one_le R 𝔍 L h𝔍 hd hn hmax T hT W hs hlev

end

end Hironaka.StepOneAdmissibleTop
