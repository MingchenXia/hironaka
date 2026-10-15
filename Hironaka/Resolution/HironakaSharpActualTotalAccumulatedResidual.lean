/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualProductRelativeStrict

/-! Actual OLD trace continuation kills exactly OLD TOTAL exponents before
WHOLE accumulated residual comparison. NEW TOTAL need not have exponent0.
Controlled positive-mark, composite original TOTAL and decrease remain OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualTotalAccumulatedResidual
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualProductRelativeStrict HironakaSharpActualProductNewExceptionalFactor
  HironakaSharpActualFiniteProductResidual HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalNoOldFactor HironakaSharpActualChronologicalStrictStep
  HironakaSharpActualFiniteChronologicalHistory
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong DivisorExponentAlong
  NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers MemberTraceIdealAlong
  GermIdealOrder BlowupSNCTransform BlowupStrictSubmanifold
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Genuine coherent continuation for ONE actual member gives its true exponent0. -/
theorem fixed_member_no_factor_divExpAlong_zero {N : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {I : GermIdeal n X} (hI : I.IsCoherent)
    (i : Fin E.length)
    (hnd : ∀ x ∈ N,x ∈ E.get i → ∃ a,I.mem x a ∧
      ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x a)
    {x : X} (hx : x ∈ N) (hxi : x ∈ E.get i) : divExpAlong n N I (E.get i) x=0 := by
  by_contra hne
  have hpos : 1 ≤ divExpAlong n N I (E.get i) x := Nat.one_le_iff_ne_zero.mpr hne
  have hhol := fun y g (hg : I.mem y g) => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg
  have hdiv := (isDivNearAlong_divExpAlong hhol x).mono hpos
  obtain ⟨a,ha,hna⟩ := hnd x hx hxi
  apply hna
  apply (isInSpanOnAt_vanishingIdeal_iff_mem hE hT hx i (hhol x a ha)).mpr
  refine ⟨hhol x a ha,?_⟩
  filter_upwards [hdiv,HadamardBridge.eventually_mem_of_isCoherent hI ha] with y hy hya hyNH
  exact (vanishesToOrderOn_one_iff hyNH.1 (hhol y a hya)).mp ((hy hyNH.1 hyNH.2).2 a hya)

/-- Actual OLD strict-trace continuation gives WHOLE monomial equality; no
NEW-member exclusion is asserted for TOTAL. -/
theorem nextTotal_accumulated_monomial_eq_new {N C : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I : GermIdeal n X} (hI : I.IsCoherent) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hCN : C ⊆ N) (hNC : HasNormalCrossings n C E)
    (hnd : ∀ x ∈ N,∀ i : Fin E.length,x ∈ E.get i → ∃ a,I.mem x a ∧
      ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x a) :
    monomialPartAlong n (nextTotalMarked N I C π).N (nextTotalMarked N I C π).ideal
      (E.map (geoStrictTransform π C) ++ [π ⁻¹' C])=
    monomialPartAlong n (nextTotalMarked N I C π).N (nextTotalMarked N I C π).ideal [π ⁻¹' C] := by
  let M : MarkedIdeal n X := ⟨N,E,I,0⟩
  have hwM : M.IsWellFormed := ⟨hN,hI,hE,hT⟩
  have hadm : M.IsAdmissibleCentre C := by
    refine ⟨hπ.1,?_,hNC⟩
    change C ⊆ cosupport n N I 0
    rw [cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
    exact hCN
  have hwNew := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hwM hadm hπ
  let E' := E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  have hzero : ∀ y ∈ (nextTotalMarked N I C π).N,∀ j : Fin E.length,y ∈ geoStrictTransform π C (E.get j) →
      divExpAlong n (nextTotalMarked N I C π).N (nextTotalMarked N I C π).ideal (geoStrictTransform π C (E.get j)) y=0 := by
    intro y hy j hyj
    let idx : Fin E'.length := ⟨j.val,by simpa only [E',List.length_append,List.length_map,List.length_singleton] using Nat.lt_succ_of_lt j.isLt⟩
    have hget : E'.get idx=geoStrictTransform π C (E.get j) := by
      rw [get_map_append_singleton]
      change (if h : j.val<E.length then geoStrictTransform π C (E.get ⟨j.val,h⟩) else π ⁻¹' C)=_
      rw [dif_pos j.isLt]
    have hnd' : ∀ z ∈ (nextTotalMarked N I C π).N,z ∈ E'.get idx → ∃ a,(nextTotalMarked N I C π).ideal.mem z a ∧
        ¬IsInSpanOnAt (n := n) (nextTotalMarked N I C π).N ((vanishingIdeal (n := n) (E'.get idx)).mem z) z a := by
      rw [hget]
      intro z hz hzi
      exact nextTotal_old_strict_member_not_factor hN hE hT hI hπ hCN hNC hnd hz j hzi
    have hz := fixed_member_no_factor_divExpAlong_zero hwNew.isSNCDivisor hwNew.isTransverse hwNew.isCoherent idx hnd' hy
    change y ∈ E'.get idx → divExpAlong n (nextTotalMarked N I C π).N (nextTotalMarked N I C π).ideal (E'.get idx) y=0 at hz
    rw [hget] at hz
    exact hz hyj
  let last : Fin E'.length := ⟨E.length,by simp [E']⟩
  have hlast : E'.get last=π ⁻¹' C := by
    rw [get_map_append_singleton]
    change (if h : E.length<E.length then geoStrictTransform π C (E.get ⟨E.length,h⟩) else π ⁻¹' C)=_
    rw [dif_neg (Nat.lt_irrefl _)]
  ext y g
  constructor
  · intro hg
    refine ⟨hg.1,?_⟩
    intro i hyN hyi
    have hi : i=(0 : Fin [π ⁻¹' C].length) := by
      apply Fin.ext
      have hh := i.isLt
      simp only [List.length_singleton] at hh
      change i.val=0
      omega
    subst i
    have hh := hg.2 last hyN
    rw [hlast] at hh
    exact hh hyi
  · intro hg
    refine ⟨hg.1,?_⟩
    intro i hyN hyi
    have hget := get_map_append_singleton E (geoStrictTransform π C) (π ⁻¹' C) i
    by_cases hi : i.val<E.length
    · rw [dif_pos hi] at hget
      rw [hget,hzero y hyN ⟨i.val,hi⟩ (hget ▸ hyi),idealPow_zero]
      exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hg.1 hg.1)
    · rw [dif_neg hi] at hget
      rw [hget]
      exact hg.2 (0 : Fin [π ⁻¹' C].length) hyN (hget ▸ hyi)

/-- Genuine full-list TOTAL residual is the independently constructed next STRICT. -/
theorem nextTotal_accumulated_nonmonomial_eq_nextStrict (hn : 0 < n) {N C : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    (hpr : ∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,I.mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (hNC : HasNormalCrossings n C E)
    (hnd : ∀ x ∈ N,∀ i : Fin E.length,x ∈ E.get i → ∃ a,I.mem x a ∧
      ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x a) :
    nonmonomialPartAlong n (nextTotalMarked N I C π).N (nextTotalMarked N I C π).ideal
      (E.map (geoStrictTransform π C) ++ [π ⁻¹' C])=nextRelativeStrict N I C π := by
  have hM := nextTotal_accumulated_monomial_eq_new hN hE hT hI hπ hCN hNC hnd
  change InvertibleIdealQuotient.colon (restrictOn n (nextTotalMarked N I C π).N (nextTotalMarked N I C π).ideal) _=_
  rw [hM]
  exact (nextRelativeStrict_actual_geometry hn hN hI hnz hpr hπ hCN).1.symm

/-- ONLY original histories internally supply full-product OLD factor exclusion
before the WHOLE actual ALL-boundary residual/next-product identity. -/
theorem original_next_total_all_accumulated_residual_eq_product (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {Z : CMfd.{u} n} (T : BlowupTower X Z) (ht : IsGeoTestTower (geometricTemplate W []) T)
    {C : Set Z} {π : Y → Z} (hπ : IsBlowupAlong n C π)
    (hCN : C ⊆ (geoTransformAlong (geometricTemplate W []) T).N)
    (hNC : HasNormalCrossings n C (geoTransformAlong (geometricTemplate W []) T).E) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let Q := nextTotalMarked A.N (chronologicalMemberProduct W E T) C π
    nonmonomialPartAlong n Q.N Q.ideal (A.E.map (geoStrictTransform π C) ++ [π ⁻¹' C])=
      chronologicalMemberProduct W E (.step T C π hπ) := by
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T ht
  obtain ⟨hc,hnz,hpr,_hord⟩ := original_chronological_full_product_actual_geometry hn hW hE hdense T ht
  have hnd := original_chronological_product_no_exceptional_factor hn hW hE hdense T ht
  exact (nextTotal_accumulated_nonmonomial_eq_nextStrict hn hwA.isClosedSubmanifold_N
    hwA.isSNCDivisor hwA.isTransverse hc hnz hpr hπ hCN hNC hnd).trans
      (original_next_chronological_product_eq_full_relative_strict hn hW hE hdense T ht hπ hCN)

end
end Hironaka.HironakaSharpActualTotalAccumulatedResidual
