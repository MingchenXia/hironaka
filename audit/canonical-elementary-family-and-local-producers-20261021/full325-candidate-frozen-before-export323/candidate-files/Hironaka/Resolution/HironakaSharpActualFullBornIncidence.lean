/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualDynamicDistinctCentre
import Hironaka.Resolution.HironakaOriginalCompanionChronologicalBoundaryAnalytic

/-! The actual FULL companion level retains every born-boundary incidence.
Original ambient trace-factor compatibility, modified decrease and termination
are separate obligations; ordinary first-order maxima are not substituted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFullBornIncidence
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings NonmonomialOrderLocal CanonicalCentres
  HironakaOriginalCompanionChronologicalBoundaryAnalytic HironakaSharpActualDynamicDistinctCentre
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteMemberProduct
  HironakaSharpOriginalProductTraceOrder BoundaryCount StepOneRegime GeneralValue
  HironakaSharpActualFiniteChronologicalHistory ResolutionDriver
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X : CMfd.{u} n}

private theorem positive_refl_threshold_iff_count (hn : 0 < n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M) {x : X} (hx : x ∈ M.cosupp)
    {q : ℕ} (hq : 1 ≤ q) (hxq : nmOrd M x=q) (s : ℕ) :
    positiveCanonicalCompanionCountThreshold k q s ≤
      (invFamily hn (k+1)).inv M (.refl : BlowupTower X X) x ↔ s ≤ boundaryCount M.E x := by
  have hset := canonical_positive_companion_count_superlevel_eq_union hn M hM
    (.refl : BlowupTower X X) trivial q s hq
  have hmem := congrArg (fun A : Set X => x ∈ A) hset
  have hnot : x ∉ ordGe M (q+1) := by
    rw [mem_ordGe_iff hM.isWellFormed hM.isNonzeroAlongAt (M.cosupp_subset_N hx),hxq]
    omega
  simpa only [geoTransformAlong_refl,Set.mem_ofPred_eq,Set.mem_union,Set.mem_inter_iff,hx,
    true_and,hnot,false_and,false_or,hxq,le_refl,companionChronologicalCount,
    chronologicalMembers,regimeRun_refl,BlowupTower.length_refl,Nat.zero_sub,
    Nat.add_zero,List.take_length,true_and] using (Iff.of_eq hmem)

/-- Equal positive original FULL values retain actual whole boundary counts,
including special companion values; no level or numerical certificate. -/
theorem boundaryCount_eq_of_full_refl_eq (hn : 0 < n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M) {x y : X}
    (hx : x ∈ M.cosupp) (hy : y ∈ M.cosupp) (hpos : 0 < nmOrd M x)
    (heq : (invFamily hn (k+1)).inv M (.refl : BlowupTower X X) x=
      (invFamily hn (k+1)).inv M (.refl : BlowupTower X X) y) :
    boundaryCount M.E x=boundaryCount M.E y := by
  have hfirst := congrArg (fun v : ValTy (k+1) => (ofLex v).1) heq
  change nmOrd (geoTransformAlong M (.refl : BlowupTower X X)) x=
    nmOrd (geoTransformAlong M (.refl : BlowupTower X X)) y at hfirst
  rw [geoTransformAlong_refl] at hfirst
  have hxthr := positive_refl_threshold_iff_count hn M hM hx hpos rfl
  have mythr := positive_refl_threshold_iff_count hn M hM hy hpos hfirst.symm
  apply Nat.le_antisymm
  · apply (mythr (boundaryCount M.E x)).mp
    rw [←heq]
    exact (hxthr _).mpr le_rfl
  · apply (hxthr (boundaryCount M.E y)).mp
    rw [heq]
    exact (mythr _).mpr le_rfl

/-- Actual FULL-value constancy gives equality of every finite incidence set
locally along the stratum, not just equality of its cardinality. -/
theorem eventually_born_incidence_of_constant_full_refl (hn : 0 < n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M) {C : Set X}
    (hC : C ⊆ M.cosupp) (hpos : ∀ x ∈ C,0 < nmOrd M x)
    (hval : ∀ x ∈ C,∀ y ∈ C,(invFamily hn (k+1)).inv M (.refl : BlowupTower X X) x=
      (invFamily hn (k+1)).inv M (.refl : BlowupTower X X) y) {x : X} (hx : x ∈ C) :
    ∀ᶠ y in 𝓝 x,y ∈ C → ∀ i : Fin M.E.length,(y ∈ M.E.get i ↔ x ∈ M.E.get i) := by
  have hclosed := hM.isWellFormed.isSNCDivisor.1
  have havoid : ∀ᶠ y in 𝓝 x,∀ i : Fin M.E.length,x ∉ M.E.get i → y ∉ M.E.get i := by
    apply eventually_all.mpr
    intro i
    by_cases hi : x ∈ M.E.get i
    · exact Eventually.of_forall fun _ h => (h hi).elim
    · filter_upwards [(hclosed _ (List.get_mem M.E i)).isOpen_compl.mem_nhds hi] with y hy _
      exact hy
  filter_upwards [havoid] with y hy hyC
  let sx := Finset.univ.filter fun i : Fin M.E.length => x ∈ M.E.get i
  let sy := Finset.univ.filter fun i : Fin M.E.length => y ∈ M.E.get i
  have hsub : sy ⊆ sx := by
    intro i hi
    simp only [sy,sx,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    by_contra hxi
    exact hy i hxi hi
  have hcount := boundaryCount_eq_of_full_refl_eq hn M hM (hC hx) (hC hyC) (hpos x hx) (hval x hx y hyC)
  have hcard : sx.card ≤ sy.card := hcount.le
  have he : sy=sx := Finset.eq_of_subset_of_card_le hsub hcard
  intro i
  have hi := Finset.ext_iff.mp he i
  simpa only [sy,sx,Finset.mem_filter,Finset.mem_univ,true_and] using hi

/-- Original-only actual FIRST maximum supplies genuine FULL equality and
every born incidence law internally on the SAME chosen admissible centre. -/
theorem exists_actual_dynamic_distinct_centre_born_incidence (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hK : IsCompact W) {d : ℕ} (hd : d+1 ≤ n)
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (ht : IsGeoTestTower (geometricTemplate W []) T)
    (hne : (chronologicalDistinctDefect W E T).Nonempty) :
    ∃ C : Set Y,C.Nonempty ∧ C ⊆ chronologicalDistinctDefect W E T ∧
      (currentProductMarked W E T).IsAdmissibleCentre C ∧
      (geoTransformAlong (geometricTemplate W []) T).IsAdmissibleCentre C ∧
      C=maxLocus ((invFamily hn (n+1)).inv (currentProductMarked W E T) (.refl : BlowupTower Y Y))
        (chronologicalDistinctDefect W E T) ∧
      ∀ x ∈ C,∀ᶠ y in 𝓝 x,y ∈ C → ∀ i : Fin (currentProductMarked W E T).E.length,
        (y ∈ (currentProductMarked W E T).E.get i ↔ x ∈ (currentProductMarked W E T).E.get i) := by
  obtain ⟨C,hneC,hCZ,hCur,hTemp,hCeq⟩ := exists_actual_dynamic_distinct_max_centre
    hn hW hE hdense hK hd hr T ht hne
  have hdom := currentProductMarked_isInvDomain hn hW hE hdense hK hd hr T ht
  have hpos : ∀ x ∈ C,0 < nmOrd (currentProductMarked W E T) x := by
    intro x hx
    have hz := (hCZ hx).2
    rw [← chronological_product_eq_actual_family_product W E T] at hz
    rw [currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T ht]
    omega
  refine ⟨C,hneC,hCZ,hCur,hTemp,hCeq,?_⟩
  intro x hx
  apply eventually_born_incidence_of_constant_full_refl hn _ hdom hCur.2.1 hpos
    (fun a ha b hb => ?_) hx
  exact ((hCeq ▸ hb).2 a (hCeq ▸ ha).1).antisymm ((hCeq ▸ ha).2 b (hCeq ▸ hb).1)

end
end Hironaka.HironakaSharpActualFullBornIncidence
