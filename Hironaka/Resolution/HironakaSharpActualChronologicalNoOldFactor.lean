/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualFiniteChronologicalHistory

/-! Genuine old strict-trace continuation before actual ALL accumulated-member
factor exclusion for independently defined iterated NEW-exceptional saturation.
Composite raw-TOTAL factor transport and sharp driver remain OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualChronologicalNoOldFactor
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalStrictStep
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong DivisorExponentAlong
  NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder BlowupStrictSubmanifold
  BlowupSNCTransform MemberTraceIdealAlong
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual strict trace continuation gives a TRUE TOTAL germ outside an OLD
strict-member ideal, without a new-exceptional order-bound premise. -/
theorem nextTotal_old_strict_member_not_factor {N C : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I : GermIdeal n X} (hI : I.IsCoherent) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hCN : C ⊆ N) (hNC : HasNormalCrossings n C E)
    (hnd : ∀ x ∈ N,∀ i : Fin E.length,x ∈ E.get i → ∃ a,I.mem x a ∧
      ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x a)
    {y : Y} (hy : y ∈ (nextTotalMarked N I C π).N) (i : Fin E.length)
    (hyi : y ∈ geoStrictTransform π C (E.get i)) :
    ∃ g,(nextTotalMarked N I C π).ideal.mem y g ∧
      ¬IsInSpanOnAt (n := n) (nextTotalMarked N I C π).N
        ((vanishingIdeal (n := n) (geoStrictTransform π C (E.get i))).mem y) y g := by
  let M : MarkedIdeal n X := ⟨N,E,I,0⟩
  have hCb : C ⊆ M.cosupp := by
    change C ⊆ cosupport n N I 0
    rw [cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
    exact hCN
  have hinter := ExceptionalPushforwardAlong.geoStrictTransform_inter_eq hπ hN.1 hCN hE hT hNC i
  have hyA : y ∈ geoStrictTransform π C (E.get i ∩ N) := hinter.symm ▸ ⟨hyi,hy⟩
  have hnot : ∀ᶠ x in 𝓝 (π y),x ∈ (E.get i ∩ N) \ C →
      ∃ a,I.mem x a ∧ ¬(vanishingIdeal (n := n) (E.get i ∩ N)).mem x a := by
    refine Eventually.of_forall fun x hx => ?_
    obtain ⟨a,ha,hna⟩ := hnd x hx.1.2 i hx.1.1
    refine ⟨a,ha,fun hmem => hna ?_⟩
    rw [isInSpanOnAt_vanishingIdeal_iff_mem hE hT hx.1.2 i
      (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI ha),Set.inter_comm]
    exact hmem
  obtain ⟨g,hg,hng⟩ := ExceptionalPushforwardAlong.exists_not_mem_vanishingIdeal_of_geoTransform hπ
    (𝔪 := M) hN hI hCb inter_subset_right hyA hnot
  refine ⟨g,hg,fun hspan => hng ?_⟩
  have hgHol : HolomorphicAt n g y := hg.1
  have hEnew := actual_accumulated_exceptional_geometry hN hI hE hT hπ hCN hNC
  let hidx : Fin (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).length :=
    ⟨i.val,by simpa only [List.length_append,List.length_map,List.length_singleton] using Nat.lt_succ_of_lt i.isLt⟩
  have hget : (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get hidx=geoStrictTransform π C (E.get i) := by
    rw [get_map_append_singleton]
    change (if h : i.val<E.length then geoStrictTransform π C (E.get ⟨i.val,h⟩) else π ⁻¹' C)=_
    rw [dif_pos i.isLt]
  have htrace := (isInSpanOnAt_vanishingIdeal_iff_mem hEnew.1 hEnew.2 hy hidx hgHol).mp (hget.symm ▸ hspan)
  rw [hget,Set.inter_comm] at htrace
  change (vanishingIdeal (n := n) (geoStrictTransform π C (E.get i) ∩ geoStrictTransform π C N)).mem y g at htrace
  rw [← hinter] at htrace
  exact htrace

/-- Genuine old continuation and NEW maximal-factor exclusion construct all
actual accumulated-member witnesses for the independent next saturation. -/
theorem nextRelativeStrict_no_accumulated_member_factor (hn : 0 < n) {N C : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    (hpr : ∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (hNC : HasNormalCrossings n C E)
    (hnd : ∀ x ∈ N,∀ i : Fin E.length,x ∈ E.get i → ∃ a,I.mem x a ∧
      ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x a)
    {y : Y} (hy : y ∈ (nextTotalMarked N I C π).N)
    (i : Fin (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).length)
    (hyi : y ∈ (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get i) :
    ∃ g,(nextRelativeStrict N I C π).mem y g ∧
      ¬IsInSpanOnAt (n := n) (nextTotalMarked N I C π).N
        ((vanishingIdeal (n := n) ((E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get i)).mem y) y g := by
  let M : MarkedIdeal n X := ⟨N,[],I,0⟩
  have hw : M.IsWellFormed := ⟨hN,hI,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩
  have hCb : C ⊆ M.cosupp := by
    change C ⊆ cosupport n N I 0
    rw [cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
    exact hCN
  have hadm : M.IsAdmissibleCentre C := ⟨hπ.1,hCb,hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1⟩
  have hwP := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw hadm hπ
  have hnzP := HironakaCoherentTransformExtension.isNonzeroAlongAt_geoTransform_without_admissibility M hN hI hπ hCN hnz
  obtain ⟨hS,_hcoh,_hnzS,_hprS,_hfactor⟩ := nextRelativeStrict_actual_geometry hn hN hI hnz hpr hπ hCN
  have hget := get_map_append_singleton E (geoStrictTransform π C) (π ⁻¹' C) i
  by_cases hi : i.val<E.length
  · rw [dif_pos hi] at hget
    have hyold : y ∈ geoStrictTransform π C (E.get ⟨i.val,hi⟩) := hget ▸ hyi
    obtain ⟨g,hg,hng⟩ := nextTotal_old_strict_member_not_factor hN hE hT hI hπ hCN hNC hnd hy ⟨i.val,hi⟩ hyold
    refine ⟨g,?_,?_⟩
    · rw [hS]
      exact NonmonomialTransformAlong.le_nonmonomialPartAlong_self hwP.isCoherent y g hg
    · rw [hget]
      exact hng
  · rw [dif_neg hi] at hget
    have hyD : y ∈ π ⁻¹' C := hget ▸ hyi
    obtain ⟨g,hg,hng⟩ := exists_mem_nonmonomialPartAlong_not hn hwP.isClosedSubmanifold_N
      hwP.isSNCDivisor hwP.isTransverse hwP.isCoherent hnzP hy (i := (0 : Fin [π ⁻¹' C].length)) hyD
    refine ⟨g,?_,?_⟩
    · rw [hS]
      exact hg
    · rw [hget]
      exact hng

/-- Literal finite geometry induction supplies actual no-common-factor germs
for the ENTIRE actual accumulated ordered list at every true prefix. -/
theorem chronologicalMarked_no_member_factor (hn : 0 < n) (M : MarkedIdeal n X)
    (hw : M.IsWellFormed) (hm : M.d=0) (hnz : ∀ x ∈ M.N,IsNonzeroAlongAt M.N M.ideal x)
    (hpr : ∀ x ∈ M.N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,M.ideal.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) M.N (·=f) x g)
    (hnd : ∀ x ∈ M.N,∀ i : Fin M.E.length,x ∈ M.E.get i → ∃ a,M.ideal.mem x a ∧
      ¬IsInSpanOnAt (n := n) M.N ((vanishingIdeal (n := n) (M.E.get i)).mem x) x a) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (geometricTemplate M.N M.E) T →
      ∀ y ∈ (chronologicalMarked M T).N,∀ i : Fin (chronologicalMarked M T).E.length,
        y ∈ (chronologicalMarked M T).E.get i → ∃ a,(chronologicalMarked M T).ideal.mem y a ∧
          ¬IsInSpanOnAt (n := n) (chronologicalMarked M T).N
            ((vanishingIdeal (n := n) ((chronologicalMarked M T).E.get i)).mem y) y a
  | _, .refl, _, y, hy, i, hi => hnd y hy i hi
  | _, .step T C π hπ, hT, y, hy, i, hi => by
    obtain ⟨hwA,hnzA,hprA⟩ := chronologicalMarked_actual_geometry hn M hw hm hnz hpr T hT.1
    obtain ⟨hAN,hAE⟩ := chronologicalMarked_geometric_fields M T
    have hCN : C ⊆ (chronologicalMarked M T).N := by rw [hAN]; exact hT.2.subset_N
    have hNC : HasNormalCrossings n C (chronologicalMarked M T).E := by rw [hAE]; exact hT.2.2.2
    exact nextRelativeStrict_no_accumulated_member_factor hn hwA.isClosedSubmanifold_N hwA.isSNCDivisor
      hwA.isTransverse hwA.isCoherent hnzA hprA hπ hCN hNC
      (chronologicalMarked_no_member_factor hn M hw hm hnz hpr hnd T hT.1) hy i hi

/-- ONLY original inputs internally supply all initial data; the ACTUAL EMPTY
initial exceptional index supplies no-factor vacuously, without a caller cert. -/
theorem original_members_actual_finite_chronological_no_exceptional_factor (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i : Fin E.length)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
    ∀ y ∈ A.N,∀ j : Fin A.E.length,y ∈ A.E.get j → ∃ a,A.ideal.mem y a ∧
      ¬IsInSpanOnAt (n := n) A.N ((vanishingIdeal (n := n) (A.E.get j)).mem y) y a := by
  let M := originalRelativeMemberMarked W (E.get i)
  obtain ⟨_hN,_hE,_hm,hwM,hnzM,hprM⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i
    (.refl : BlowupTower X X) trivial
  have hnd : ∀ x ∈ M.N,∀ j : Fin M.E.length,x ∈ M.E.get j → ∃ a,M.ideal.mem x a ∧
      ¬IsInSpanOnAt (n := n) M.N ((vanishingIdeal (n := n) (M.E.get j)).mem x) x a := by
    intro x hx j
    exact Fin.elim0 j
  exact chronologicalMarked_no_member_factor hn M hwM rfl hnzM hprM hnd T hT

end
end Hironaka.HironakaSharpActualChronologicalNoOldFactor
