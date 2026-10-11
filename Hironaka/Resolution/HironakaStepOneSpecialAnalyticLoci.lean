/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaMonomialAnalyticSuperlevels

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

/-!
# Actual analytic member loci and Step 1 maximal-second-entry superlevels

Actual SNC intersections and analytic continuation select genuine global
components. No maximal boundary-count assumption or global finite component
family is needed. These producers are connected to the actual per-sequence
masked Step 1 value. Lower companion/history thresholds and G3 remain open.
Blueprint: `hironaka-step-one-special-superlevels-extension.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaStepOneSpecialAnalyticLoci

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open GlobalComponents RegularLocusComponent HironakaDimensionGlobalComponents
  BoundaryCount MemberInterLocusAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms StepOneValue StepOneLowerDomain CodimOneSupportAlong
  HomogenizedIdealAlong HironakaBoundaryCountAnalyticSuperlevels

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual global components of `H` which are wholly contained in `A`. -/
def selectedComponents (H A : Set M) : Set M :=
  ⋃₀ {B | B ∈ globalComponents (n := n) H ∧ B ⊆ A}

private theorem component_closed_of_smooth {H : Set M} (hH : IsClosedSubmanifold n H)
    (c : M) : closure (component (n := n) H c) = component (n := n) H c := by
  have hreg : regularPoints (n := n) H = H :=
    Subset.antisymm (regularPoints_subset H) (fun y hy => hH.2 y hy)
  have heq : component (n := n) H c = connectedComponentIn H c := by
    unfold component
    rw [hreg]
  rw [heq]
  by_cases hc : c ∈ H
  · exact Subset.antisymm
      (isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
        (subset_closure (mem_connectedComponentIn hc))
        (closure_minimal (connectedComponentIn_subset H c) hH.1)) subset_closure
  · simp [connectedComponentIn_eq_empty hc]

/-- Arbitrary selected unions of an actual smooth set's genuine global
components are closed and smooth, even when the full family is infinite. -/
theorem isClosedSubmanifold_selectedComponents {H : Set M}
    (hH : IsClosedSubmanifold n H) (A : Set M) :
    IsClosedSubmanifold n (selectedComponents (n := n) H A) := by
  have hHa := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hH
  refine ⟨isClosed_sUnion_globalComponents_subfamily hHa (fun _ h => h.1), ?_⟩
  rintro x ⟨B, ⟨hB, hBA⟩, hxB⟩
  obtain ⟨c, ⟨k, hc⟩, rfl⟩ := hB
  rw [component_closed_of_smooth hH c] at hxB
  obtain ⟨U, hU, hxU, hHU⟩ := exists_open_inter_subset_component hc hxB
  refine ⟨k, RegularPointDimension.regularAtDim_of_inter_eq hU hxU ?_
    (regularAtDim_of_mem_component hc hxB)⟩
  apply Subset.antisymm
  · intro y hy
    exact ⟨mem_sUnion.mpr ⟨closure (component (n := n) H c),
      ⟨closure_component_mem_globalComponents hc, hBA⟩, subset_closure (hHU hy)⟩, hy.2⟩
  · rintro y ⟨⟨C, ⟨hC, -⟩, hyC⟩, hyU⟩
    exact ⟨subset_of_mem_globalComponents hHa hC hyC, hyU⟩

/-- The actual member-intersection locus is precisely a finite union of
selected genuine global components of actual smooth SNC intersections. -/
theorem memberInterLocus_eq_componentUnion (hn : 0 < n) (N : Set M)
    (hN : IsClosedSubmanifold n N) (E : List (Set M)) (hE : IsSNCDivisor n E)
    (htrans : IsTransverse n N E) {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hAN : A ⊆ N) :
    memberInterLocus N E A =
      ⋃ S : Finset (Fin E.length), selectedComponents (n := n) (N ∩ memberInter E S) A := by
  classical
  have hH : ∀ S, IsClosedSubmanifold n (N ∩ memberInter E S) :=
    MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hN.1 hE htrans
  ext x
  constructor
  · intro hx
    let S := Finset.univ.filter (fun i : Fin E.length => x ∈ E.get i)
    have hxH : x ∈ N ∩ memberInter E S := by
      refine ⟨hAN hx.1, ?_⟩
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    obtain ⟨k, hk⟩ := (hH S).2 x hxH
    obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hx.2
    have hCsub : component (n := n) (N ∩ memberInter E S) x ⊆ A := by
      refine component_subset_of_isOpen hA hU
        ⟨x, hxU, mem_component_self hk⟩ ?_
      rintro y ⟨hyU, hyC⟩
      have hyH := component_subset (n := n) (N ∩ memberInter E S) x hyC
      exact hUsub hyU hyH.1
        (fun i hxi => hyH.2 i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxi⟩))
    refine mem_iUnion.mpr ⟨S, mem_sUnion.mpr
      ⟨closure (component (n := n) (N ∩ memberInter E S) x),
        ⟨closure_component_mem_globalComponents hk, closure_minimal hCsub hA.isClosed⟩,
        subset_closure (mem_component_self hk)⟩⟩
  · intro hx
    obtain ⟨S, B, ⟨hB, hBA⟩, hxB⟩ := mem_iUnion.mp hx
    have hxH := subset_of_mem_globalComponents
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold (hH S)) hB hxB
    obtain ⟨c, ⟨k, hc⟩, rfl⟩ := hB
    rw [component_closed_of_smooth (hH S) c] at hxB
    obtain ⟨U, hU, hxU, hHU⟩ := exists_open_inter_subset_component hc hxB
    refine ⟨hBA (subset_closure hxB), ?_⟩
    filter_upwards [hU.mem_nhds hxU] with y hyU hyN hyE
    exact hBA (subset_closure (hHU ⟨⟨hyN, fun i hi => hyE i (hxH.2 i hi)⟩, hyU⟩))

/-- Actual SNC geometry and actual analytic equations produce the full
member locus's global analyticity without a maximal-count assumption. -/
theorem isComplexAnalyticSubset_memberInterLocus (hn : 0 < n) (N : Set M)
    (hN : IsClosedSubmanifold n N) (E : List (Set M)) (hE : IsSNCDivisor n E)
    (htrans : IsTransverse n N E) {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hAN : A ⊆ N) : IsComplexAnalyticSubset (n := n) (memberInterLocus N E A) := by
  classical
  rw [memberInterLocus_eq_componentUnion hn N hN E hE htrans hA hAN]
  let L := (Finset.univ : Finset (Finset (Fin E.length))).toList.map
    (fun S => (selectedComponents (n := n) (N ∩ memberInter E S) A, S))
  have hL := HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_biUnion_list L (by
    intro p hp
    obtain ⟨S, -, rfl⟩ := List.mem_map.mp hp
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (isClosedSubmanifold_selectedComponents
        (MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hN.1 hE htrans S) A))
  have heq : (⋃ p ∈ L, p.1) =
      ⋃ S : Finset (Fin E.length), selectedComponents (n := n) (N ∩ memberInter E S) A := by
    ext x
    simp [L]
  rwa [heq] at hL

section ActualStepOne

universe u v
variable {k : ℕ} {X Y : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- At actual cosupport points the genuine masked lower value is never junk
top. Thus the whole top-second-entry threshold has this exact dictionary. -/
theorem stepOneInvM_top_threshold_iff
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    (hn : 0 < n) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T)
    {y : Y} (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) (s : ℕ) :
    toLex (s, (⊤ : WithTop Λ)) ≤ Seq.StepOneValueMasked.stepOneInvM R 𝔍 T y ↔
      s < level 𝔍 T y ∨ (s = level 𝔍 T y ∧ IsSpecial 𝔍 T y) := by
  classical
  by_cases hsp : IsSpecial 𝔍 T y
  · simp [Seq.StepOneValueMasked.stepOneInvM, Seq.StepOneValueMasked.stepOneInvL,
      hsp, Prod.Lex.toLex_le_toLex]
  · have hne := Seq.StepOneValueMasked.lowerValueL_ne_top (R := R) 𝔍 h𝔍 hd hn hmax
      (StepOneValueMasked.lowerMarkedM 𝔍) T hT hy hsp
    simp [Seq.StepOneValueMasked.stepOneInvM, Seq.StepOneValueMasked.stepOneInvL,
      hsp, Prod.Lex.toLex_le_toLex, hne]

/-- Genuine derivative ideals, actual SNC intersections and actual maximal
order internally produce every whole Step 1 top-second-entry superlevel. -/
theorem isComplexAnalyticSubset_stepOneInvM_top_superlevel
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    (hn : 0 < n) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T) (s : ℕ) :
    IsComplexAnalyticSubset (n := n)
      {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        toLex (s, (⊤ : WithTop Λ)) ≤ Seq.StepOneValueMasked.stepOneInvM R 𝔍 T y} := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T hT
  have hdT : 1 ≤ (geoTransformAlong (barMarked 𝔍) T).d := by
    rw [d_geoTransformAlong]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hmaxT := isMaximalOrderAlong_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent
    (isMaximalOrderAlong_barMarked 𝔍 h𝔍 hd hmax) T hT
  have hA := isComplexAnalyticSubset_cosupport_along hwf.isCoherent hwf.isClosedSubmanifold_N hdT
  have hE := NormalCrossingsComparison.isSNCDivisor_of_sublist hwf.isSNCDivisor
    (List.take_sublist 𝔍.E.length (geoTransformAlong (barMarked 𝔍) T).E)
  have htr : IsTransverse n (geoTransformAlong (barMarked 𝔍) T).N (origMembers 𝔍 T) :=
    NormalCrossingsComparison.isTransverse_of_forall_mem hwf.isTransverse
      (fun H hH => List.take_subset 𝔍.E.length _ hH)
  have hL := isComplexAnalyticSubset_memberInterLocus hn _ hwf.isClosedSubmanifold_N
    (origMembers 𝔍 T) hE htr hA (geoTransformAlong (barMarked 𝔍) T).cosupp_subset_N
  cases s with
  | zero =>
    have hZ := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (isClosedSubmanifold_codimOnePartAlong hwf.isCoherent hwf.isClosedSubmanifold_N hdT hmaxT)
    have heq : {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        toLex (0, (⊤ : WithTop Λ)) ≤ Seq.StepOneValueMasked.stepOneInvM R 𝔍 T y} =
        ((geoTransformAlong (barMarked 𝔍) T).cosupp ∩ {y | 1 ≤ level 𝔍 T y}) ∪
          codimOnePartAlong (geoTransformAlong (barMarked 𝔍) T).N
            (geoTransformAlong (barMarked 𝔍) T).ideal (geoTransformAlong (barMarked 𝔍) T).d := by
      ext y
      constructor
      · rintro ⟨hy, hv⟩
        rcases (stepOneInvM_top_threshold_iff R hn 𝔍 h𝔍 hd hmax T hT hy 0).mp hv with
          hpos | ⟨heq, hsp⟩
        · exact Or.inl ⟨hy, hpos⟩
        · rcases hsp with ⟨-, hz⟩ | ⟨hpos, -⟩
          · exact Or.inr hz
          · omega
      · rintro (⟨hy, hpos⟩ | hz)
        · exact ⟨hy, (stepOneInvM_top_threshold_iff R hn 𝔍 h𝔍 hd hmax T hT hy 0).mpr
            (Or.inl hpos)⟩
        · have hy := codimOnePartAlong_subset hz
          refine ⟨hy, (stepOneInvM_top_threshold_iff R hn 𝔍 h𝔍 hd hmax T hT hy 0).mpr ?_⟩
          by_cases hzero : level 𝔍 T y = 0
          · exact Or.inr ⟨hzero.symm, Or.inl ⟨hzero, hz⟩⟩
          · exact Or.inl (Nat.pos_of_ne_zero hzero)
    rw [heq]
    exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
      (hA.inter (isComplexAnalyticSubset_stepOne_level_superlevel hn 𝔍 h𝔍 T hT 1)) hZ
  | succ s =>
    have heq : {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        toLex (s + 1, (⊤ : WithTop Λ)) ≤ Seq.StepOneValueMasked.stepOneInvM R 𝔍 T y} =
        ((geoTransformAlong (barMarked 𝔍) T).cosupp ∩ {y | s + 2 ≤ level 𝔍 T y}) ∪
          (memberInterLocus (geoTransformAlong (barMarked 𝔍) T).N (origMembers 𝔍 T)
            (geoTransformAlong (barMarked 𝔍) T).cosupp ∩ {y | s + 1 ≤ level 𝔍 T y}) := by
      ext y
      constructor
      · rintro ⟨hy, hv⟩
        rcases (stepOneInvM_top_threshold_iff R hn 𝔍 h𝔍 hd hmax T hT hy (s + 1)).mp hv with
          hpos | ⟨heq, hsp⟩
        · exact Or.inl ⟨hy, show s + 2 ≤ level 𝔍 T y by omega⟩
        · rcases hsp with ⟨hzero, -⟩ | ⟨-, hl⟩
          · omega
          · exact Or.inr ⟨hl, show s + 1 ≤ level 𝔍 T y by omega⟩
      · rintro (⟨hy, hpos⟩ | ⟨hl, hle⟩)
        · change s + 2 ≤ level 𝔍 T y at hpos
          exact ⟨hy, (stepOneInvM_top_threshold_iff R hn 𝔍 h𝔍 hd hmax T hT hy (s + 1)).mpr
            (Or.inl (by omega))⟩
        · change s + 1 ≤ level 𝔍 T y at hle
          refine ⟨hl.1, (stepOneInvM_top_threshold_iff R hn 𝔍 h𝔍 hd hmax T hT hl.1 (s + 1)).mpr ?_⟩
          rcases hle.lt_or_eq with hlt | heq
          · exact Or.inl hlt
          · exact Or.inr ⟨heq, Or.inr ⟨by omega, hl⟩⟩
    rw [heq]
    exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
      (hA.inter (isComplexAnalyticSubset_stepOne_level_superlevel hn 𝔍 h𝔍 T hT (s + 2)))
      (hL.inter (isComplexAnalyticSubset_stepOne_level_superlevel hn 𝔍 h𝔍 T hT (s + 1)))

end ActualStepOne

end
end Hironaka.HironakaStepOneSpecialAnalyticLoci
