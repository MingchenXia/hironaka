/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalAllBoundaryCentre

/-! Actual deep original product centre and true whole-good-region-preserving
first blowup. Source-first mathematics precedes this implementation. No full
DISTINCT-defect driver or terminating sharp history is asserted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalDeepProductBlowup
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  NormalCrossings SimultaneousNormalCrossings NormalCrossingsInvariance
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalAllBoundaryCentre HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpSingleBoundaryTraceCentre GermIdealOrder
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

/-- The true original product's actual open pullback, proved from real coherent factors. -/
theorem pullback_val_originalMemberProduct (hn : 0 < n) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (U : Opens X) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (originalMemberProduct (n := n) E) =
      originalMemberProduct (n := n) (E.map ((Subtype.val : U → X) ⁻¹' ·)) := by
  induction E with
  | nil => exact BlowupExceptionalDivisor.pullback_unitIdeal
  | cons H E ih =>
    have hTail : IsSNCDivisor n E := NormalCrossingsComparison.isSNCDivisor_of_sublist hE
      (List.sublist_cons_self H E)
    have hH : IsClosedSubmanifold n H := originalBoundary_isClosedSubmanifold hn
      (NormalCrossingsComparison.isSNCDivisor_of_sublist hE (List.singleton_sublist.mpr (by simp)))
    change GermIdeal.pullback (m := n) (Subtype.val : U → X)
      ((vanishingIdeal (n := n) H).mul (originalMemberProduct (n := n) E)) = _
    rw [GermIdealTotalTransform.pullback_mul contMDiff_subtype_val
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hH) (isCoherent_originalMemberProduct hn hTail),
      SmoothCentreHomogeneity.pullback_val_vanishingIdeal,ih hTail]
    rfl

/-- This is the SAME complete actual product marked record on the real original open. -/
theorem pullback_val_originalMemberProductMarked (hn : 0 < n) (W : Set X) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (q : ℕ) (U : Opens X) :
    MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) (originalMemberProductMarked W E q) =
      originalMemberProductMarked (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W)
        (E.map ((Subtype.val : U → X) ⁻¹' ·)) q := by
  simp [MarkedIdealBiholomorphism.MarkedIdeal.pullback,originalMemberProductMarked,
    pullback_val_originalMemberProduct hn hE U]

/-- True deep product cosupport avoids all actual original good NC points. -/
theorem originalDeepProduct_cosupp_disjoint_good (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) :
    Disjoint (originalMemberProductMarked W E (E.length+1)).cosupp (originalGoodLocus (n := n) W E) := by
  apply Set.disjoint_left.mpr
  intro x hx hgood
  have hxW : x ∈ W := hx.1
  have hxNC : HironakaSharpNormalCrossingsOpenLocus.normalCrossingsAt (n := n) W E x := by
    rcases hgood with hout | hnc
    · exact False.elim (hout hxW)
    · exact hnc.2
  obtain ⟨U,hxU,hEU,hTU,hord⟩ := exists_actual_original_product_order_neighborhood hn hW.1 hE hdense hxNC
  let z : U := ⟨x,hxU⟩
  have hz : z ∈ (originalMemberProductMarked (X := CMfd.of (n := n) U)
      ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) (E.length+1)).cosupp := by
    rw [← pullback_val_originalMemberProductMarked hn W hE (E.length+1) U,
      MarkedIdealRestrictOpen.cosupp_pullback_val]
    · exact hx
    · exact fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        (isCoherent_originalMemberProduct hn hE) hg
  have hq := (hord z hxW (E.length+1)).mp hz
  rw [distinctProperTraceGermCount_eq_boundaryCount hn hEU hTU hxW] at hq
  have hcount : BoundaryCount.boundaryCount (E.map ((Subtype.val : U → X) ⁻¹' ·)) z ≤ E.length := by
    unfold BoundaryCount.boundaryCount
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  exact Nat.not_succ_le_self E.length (hq.trans hcount)

/-- The literal original deep cosupport lies in the true original sharp bad set. -/
theorem originalDeepProduct_cosupp_subset_sharpBad (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) :
    (originalMemberProductMarked W E (E.length+1)).cosupp ⊆ originalSharpBadLocus (n := n) W E := by
  intro x hx
  exact ⟨hx.1,fun hnc => Set.disjoint_left.mp (originalDeepProduct_cosupp_disjoint_good hn hW hE hdense)
    hx (Or.inr ⟨hx.1,hnc⟩)⟩

/-- Only original inputs internally produce the SAME actual ALL-boundary deep centre. -/
theorem exists_actual_original_deepProduct_centre (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d ≤ n) (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x d)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hcompact : IsCompact W)
    (hne : (originalMemberProductMarked W E (E.length+1)).cosupp.Nonempty) :
    ∃ C : Set X,C.Nonempty ∧ (originalMemberProductMarked W E (E.length+1)).IsAdmissibleCentre C ∧
      C ⊆ originalSharpBadLocus (n := n) W E ∧ C ⊆ W ∩ ⋃ H ∈ E,H ∧
      Disjoint C (originalGoodLocus (n := n) W E) ∧
      (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      C=ResolutionDriver.maxLocus ((CanonicalCentres.invFamily hn (n+1)).inv
        (originalMemberProductMarked W E (E.length+1)) (.refl : BlowupTower X X))
        (originalMemberProductMarked W E (E.length+1)).cosupp := by
  obtain ⟨C,hCne,hCadm,_hCW,_hNCE,hemb,hCeq⟩ :=
    exists_actual_original_allBoundary_product_centre hn hW hE hd hreg hdense
      (Nat.succ_pos E.length) hcompact hne
  have hbad : C ⊆ originalSharpBadLocus (n := n) W E := hCadm.2.1.trans
    (originalDeepProduct_cosupp_subset_sharpBad hn hW hE hdense)
  exact ⟨C,hCne,hCadm,hbad,hbad.trans (originalSharpBadLocus_subset_boundary hW),
    (originalDeepProduct_cosupp_disjoint_good hn hW hE hdense).mono_left hCadm.2.1,hemb,hCeq⟩

/-- SAME actual centre and projection: genuine whole-good preserving FIRST blowup geometry. -/
theorem exists_actual_original_deepProduct_blowup (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d ≤ n) (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x d)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hcompact : IsCompact W)
    (hne : (originalMemberProductMarked W E (E.length+1)).cosupp.Nonempty) :
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X),C.Nonempty ∧
      (originalMemberProductMarked W E (E.length+1)).IsAdmissibleCentre C ∧
      C ⊆ originalSharpBadLocus (n := n) W E ∧ C ⊆ W ∩ ⋃ H ∈ E,H ∧
      Disjoint C (originalGoodLocus (n := n) W E) ∧
      (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      IsBlowupAlong n C π ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (originalGoodLocus (n := n) W E) ∧
      IsClosedSubmanifold n (strictTransform n π W) ∧
      IsSNCDivisor n (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      C=ResolutionDriver.maxLocus ((CanonicalCentres.invFamily hn (n+1)).inv
        (originalMemberProductMarked W E (E.length+1)) (.refl : BlowupTower X X))
        (originalMemberProductMarked W E (E.length+1)).cosupp := by
  obtain ⟨C,hCne,hCadm,hbad,hboundary,hdis,hemb,hCeq⟩ :=
    exists_actual_original_deepProduct_centre hn hW hE hd hreg hdense hcompact hne
  have hdom := originalMemberProductMarked_isInvDomain hn hW hE hd hreg hdense (Nat.succ_pos E.length)
  have hint : interior C=∅ := eq_empty_of_subset_empty
    ((interior_mono hCadm.2.1).trans (ResolutionInvariantDriver.interior_cosupp_eq_empty hdom).subset)
  obtain ⟨Y,π,hπ⟩ := ResolutionDriver.exists_blowup C hCadm.1 hint
  have hGsub : originalGoodLocus (n := n) W E ⊆ Cᶜ := fun _ hz hC => Set.disjoint_left.mp hdis hC hz
  have hisoC := BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ
  have hiso : IsIsomorphismOver n π (originalGoodLocus (n := n) W E) := by
    refine ⟨⟨fun _ hz => hz,?_,?_⟩,hisoC.2.mono_left (preimage_mono hGsub)⟩
    · exact hisoC.1.2.1.mono (preimage_mono hGsub)
    · intro x hx
      obtain ⟨y,_hy,hπy⟩ := hisoC.1.2.2 (hGsub hx)
      exact ⟨y,by change π y ∈ originalGoodLocus (n := n) W E; rwa [hπy],hπy⟩
  have hdenseC : W ⊆ closure (W \ C) := hdense.trans (closure_mono (by
    rintro x ⟨hxW,hxE⟩
    exact ⟨hxW,fun hxC => hxE (hboundary hxC).2⟩))
  have hgeo := BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hdenseC
  have hW' : IsClosedSubmanifold n (strictTransform n π W) := by
    rw [← hgeo]
    exact BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold
      hπ hW (fun _ hz => (hboundary hz).1)
  have hMwell : (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
      VanishingIdealCoherent.isCoherent_vanishingIdeal hW,hE,isTransverse_univ_of_isSNCDivisor hE⟩
  have hE' := (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hMwell hemb hπ).isSNCDivisor
  exact ⟨C,Y,π,hCne,hCadm,hbad,hboundary,hdis,hemb,hπ,
    HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,hπ.contMDiff,hiso,hW',hE',hCeq⟩

end
end Hironaka.HironakaSharpOriginalDeepProductBlowup
