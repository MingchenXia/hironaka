/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGlobalSmoothStrictSets

/-! Actual natural-number boundary positions preserve empty births and
variable finite local histories before global locally finite descent. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveBirthBoundaryOverlaps
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveGlobalSmoothStrictSets
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveFullAmbientBoundary
  HironakaSharpActualCurveCommonOpenCocycle
  HironakaSharpActualCurveOverlapMaps HironakaSharpActualCurveChosenOverlapCocycle
  HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualCurveStrictSetOverlaps
  HironakaSharpActualCurveEndpointGeometry
  BlowupTowerIsoTail
  NormalCrossings NormalCrossingsInvariance SimultaneousNormalCrossings
  HironakaSharpActualCurveChosenOverlapCocycle HironakaSharpActualCurveOverlapMaps
  MaxLocusLocal
  HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupStrictSubmanifold MarkedIdealBiholomorphism BlowupTowerIsomorphism
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Every real ordered position is retained, with genuinely absent positions
read as EMPTY rather than deleting empty births. -/
def boundaryReadout {Z : Type u} (E : List (Set Z)) (k : ℕ) : Set Z := E.getD k ∅

theorem boundaryReadout_map_preimage {P Q : Type u} (f : P → Q) (E : List (Set Q)) (k : ℕ) :
    boundaryReadout (E.map (f ⁻¹' ·)) k=f ⁻¹' boundaryReadout E k := by
  simpa only [boundaryReadout,preimage_empty] using List.getD_map E (∅ : Set Q) (f ⁻¹' ·)

theorem boundaryReadout_append_empty {Z : Type u} (E : List (Set Z)) (r k : ℕ) :
    boundaryReadout (E++List.replicate r (∅ : Set Z)) k=boundaryReadout E k := by
  unfold boundaryReadout
  by_cases hk : k<E.length
  · exact List.getD_append E _ ∅ k hk
  · have hle : E.length≤k := Nat.le_of_not_gt hk
    rw [List.getD_append_right E _ ∅ k hle,List.getD_eq_default E ∅ hle]
    exact List.getElem?_getD_replicate_default_eq ∅ r (k-E.length)

private theorem empty_identity_strict {H : Set Y} (hH : IsClosed H) :
    geoStrictTransform (id : Y → Y) ∅ H=H := by
  simpa only [geoStrictTransform,Set.sdiff_empty,Set.preimage_id] using hH.closure_eq

/-- Actual identity-empty steps append actual EMPTY divisors; original
members are preserved by genuine CLOSED-set strict-transform identity. -/
theorem boundary_identityEmptyTail (M : MarkedIdeal n Y)
    (hE : ∀ H ∈ M.E,IsClosed H) (r : ℕ) :
    (geoTransformAlong M (identityEmptyTail Y r)).E=M.E++List.replicate r (∅ : Set Y) := by
  induction r with
  | zero => simp [identityEmptyTail]
  | succ r ih =>
    rw [identityEmptyTail,geoTransformAlong_step,geoTransform_E,ih,List.map_append,List.map_replicate]
    have hm : M.E.map (geoStrictTransform (id : Y → Y) ∅)=M.E := by
      have hh : M.E.map (geoStrictTransform (id : Y → Y) ∅)=M.E.map id :=
        List.map_congr_left fun H hH => empty_identity_strict (hE H hH)
      simpa only [List.map_id] using hh
    rw [hm,empty_identity_strict isClosed_empty]
    simp only [preimage_empty,List.replicate_succ',List.append_assoc]

/-- The entire TRUE finite history and all empty positions retain exactly
their old natural-number readouts after genuine identity padding. -/
theorem boundaryReadout_append_identityEmptyTail (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (hE : ∀ H ∈ (geoTransformAlong M T).E,IsClosed H) (r k : ℕ) :
    boundaryReadout (geoTransformAlong M (T.append (identityEmptyTail Y r))).E k=
      boundaryReadout (geoTransformAlong M T).E k := by
  rw [geoTransformAlong_append,boundary_identityEmptyTail _ hE,boundaryReadout_append_empty]

/-- Actual marked restriction transports EACH ordered position, including
positions beyond the whole actual finite list. -/
theorem boundaryReadout_restrict (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent) (U : Opens X)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (k : ℕ) :
    boundaryReadout (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M)
      (restrict U T)).E k=
      (Subtype.val : openPreimage T U → Y) ⁻¹' boundaryReadout (geoTransformAlong M T).E k := by
  rw [MarkedIdealRestrictOpen.geoTransformAlong_restrict U hN hI T hT]
  exact boundaryReadout_map_preimage _ _ k

/-- The cutoff is the literal original list length PLUS the entire actual
history length, never the number of nonempty members. -/
theorem boundaryReadout_geoTransformAlong_eq_empty (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (k : ℕ) (hk : M.E.length+T.length≤k) :
    boundaryReadout (geoTransformAlong M T).E k=∅ := by
  apply List.getD_eq_default
  rwa [length_E_geoTransformAlong]

/-- Ordered boundary transport uses the ACTUAL stage maps, centres and
strict transforms; it needs no ideal coherence or desired record comparison. -/
theorem boundary_field_isTowerIso {X' Y' : CMfd.{u} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (M : MarkedIdeal n X) (h : IsTowerIso Φ T' T χ) :
    (geoTransformAlong (MarkedIdeal.pullback Φ M) T').E=
      (geoTransformAlong M T).E.map (χ ⁻¹' ·) := by
  induction h with
  | refl => rfl
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    have hfun : χ ∘ π'=π ∘ χ₁ := funext fun p => (hcomm p).symm
    have hs (B : Set Y) : geoStrictTransform π' C' (χ ⁻¹' B)=
        χ₁ ⁻¹' geoStrictTransform π C B := by
      rw [←hC,←BlowupBiholomorphismLift.geoStrictTransform_comp_diffeo χ₁ π C]
      unfold geoStrictTransform
      rw [←preimage_sdiff,←preimage_comp,hfun]
    change (geoTransformAlong (MarkedIdeal.pullback Φ M) T').E.map (geoStrictTransform π' C') ++
        [π' ⁻¹' C'] =
      ((geoTransformAlong M T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).map (χ₁ ⁻¹' ·)
    rw [ih,List.map_map,List.map_append,List.map_map,List.map_cons,List.map_nil]
    congr 1
    · exact List.map_congr_left fun B _ => hs B
    · congr 1
      rw [←hC]
      ext p
      change χ (π' p)∈C ↔ π (χ₁ p)∈C
      rw [hcomm]

/-- ALL natural-number positions transport, including genuine empty births
and positions outside both lists. -/
theorem boundaryReadout_isTowerIso {X' Y' : CMfd.{u} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (M : MarkedIdeal n X) (h : IsTowerIso Φ T' T χ) (k : ℕ) :
    boundaryReadout (geoTransformAlong (MarkedIdeal.pullback Φ M) T').E k=
      χ ⁻¹' boundaryReadout (geoTransformAlong M T).E k := by
  rw [boundary_field_isTowerIso M h,boundaryReadout_map_preimage]

/-- BOTH genuine marked open restrictions are taken before the REAL empty
tail. Their entire ordered readout is the original endpoint trace. -/
theorem localPaddedHistory_boundaryReadout (U O : Opens X) {Z : CMfd.{u} n}
    (M : MarkedIdeal n (CMfd.of (n := n) U)) (hM : M.IsWellFormed)
    (P : BlowupTower (CMfd.of (n := n) U) Y) (S : BlowupTower Y Z)
    (hT : IsGeoTestTower M (P.append S)) (L k : ℕ) :
    boundaryReadout (geoTransformAlong
      (MarkedIdeal.pullback (Subtype.val : nestedOpens U O → U) M)
      (localPaddedHistory U O P S L)).E k=
      (Subtype.val : localEndpoint U O P S → Z) ⁻¹'
        boundaryReadout (geoTransformAlong M (P.append S)).E k := by
  obtain ⟨hP,hS⟩ := (isGeoTestTower_append_iff M P S).mp hT
  have hwP := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM P hP
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM (P.append S) hT
  have hPrefix := MarkedIdealRestrictOpen.geoTransformAlong_restrict (nestedOpens U O)
    hM.isClosedSubmanifold_N hM.isCoherent P hP
  have hBoth : geoTransformAlong
      (MarkedIdeal.pullback (Subtype.val : nestedOpens U O → U) M)
      ((restrict (nestedOpens U O) P).append (restrict (openPreimage P (nestedOpens U O)) S))=
      MarkedIdeal.pullback (Subtype.val : localEndpoint U O P S → Z)
        (geoTransformAlong M (P.append S)) := by
    rw [geoTransformAlong_append,hPrefix,
      MarkedIdealRestrictOpen.geoTransformAlong_restrict (openPreimage P (nestedOpens U O))
        hwP.isClosedSubmanifold_N hwP.isCoherent S hS,geoTransformAlong_append]
  have hClosed : ∀ H ∈ (geoTransformAlong
      (MarkedIdeal.pullback (Subtype.val : nestedOpens U O → U) M)
      ((restrict (nestedOpens U O) P).append (restrict (openPreimage P (nestedOpens U O)) S))).E,
      IsClosed H := by
    rw [hBoth]
    intro H hH
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hH
    exact (hwT.isSNCDivisor.1 B hB).preimage continuous_subtype_val
  dsimp only [localPaddedHistory,paddedHistory]
  rw [←BlowupTower.append_assoc,boundaryReadout_append_identityEmptyTail _ _ hClosed,hBoth]
  exact boundaryReadout_map_preimage _ _ k

/-- The actual local ledger contains original positions followed by EVERY
real exceptional birth; its length is allowed to depend on the chart. -/
def localBoundaryReadout {J : Type u} (A : ActualEndpointHistories X J)
    (E : List (Set X)) (i : J) (k : ℕ) : Set (A.finalSpace i) :=
  boundaryReadout (geoTransformAlong
    (geometricTemplate (univ : Set (A.openSet i)) (E.map ((Subtype.val : A.openSet i → X) ⁻¹' ·)))
    ((A.prefixTower i).append (A.tail i))).E k

private theorem ambientTemplate_wellFormed {Q : CMfd.{u} n}
    (E : List (Set Q)) (hE : IsSNCDivisor n E) :
    (geometricTemplate (univ : Set Q) E).IsWellFormed :=
  ⟨⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩,
    IdealWeightPowers.isCoherent_unitIdeal,hE,isTransverse_univ_of_isSNCDivisor hE⟩

/-- Genuine TESTs are ordinary geometric inputs to this helper. The
original-only consumer below supplies ALL of them internally. -/
theorem comparison_localBoundaryReadout {J : Type u} (A : ActualEndpointHistories X J)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hT : ∀ i : J,IsGeoTestTower
      (geometricTemplate (univ : Set (A.openSet i)) (E.map ((Subtype.val : A.openSet i → X) ⁻¹' ·)))
      ((A.prefixTower i).append (A.tail i))) (i j : J) (k : ℕ)
    (z : localEndpoint (A.openSet i) (A.openSet i⊓A.openSet j) (A.prefixTower i) (A.tail i)) :
    (A.comparison i j z).val∈localBoundaryReadout A E j k ↔ z.val∈localBoundaryReadout A E i k := by
  let Mi := geometricTemplate (X := CMfd.of (n := n) (A.openSet i))
    univ (E.map ((Subtype.val : A.openSet i → X) ⁻¹' ·))
  let Mj := geometricTemplate (X := CMfd.of (n := n) (A.openSet j))
    univ (E.map ((Subtype.val : A.openSet j → X) ⁻¹' ·))
  let O := A.openSet i⊓A.openSet j
  let Φ := commonOpenBase (A.openSet i) (A.openSet j) O inf_le_left inf_le_right
  have hi : Mi.IsWellFormed := ambientTemplate_wellFormed _
    (isSNCDivisor_map_preimage (pullsBackCoordinates_val (A.openSet i)) continuous_subtype_val hE)
  have hj : Mj.IsWellFormed := ambientTemplate_wellFormed _
    (isSNCDivisor_map_preimage (pullsBackCoordinates_val (A.openSet j)) continuous_subtype_val hE)
  have hInitial : (MarkedIdeal.pullback Φ
      (MarkedIdeal.pullback (Subtype.val : nestedOpens (A.openSet j) O → A.openSet j) Mj)).E=
      (MarkedIdeal.pullback (Subtype.val : nestedOpens (A.openSet i) O → A.openSet i) Mi).E := by
    simp only [MarkedIdeal.pullback,Mi,Mj,geometricTemplate,List.map_map]
    rfl
  have h := boundaryReadout_isTowerIso
    (MarkedIdeal.pullback (Subtype.val : nestedOpens (A.openSet j) O → A.openSet j) Mj)
    (A.stagewise i j) k
  rw [HironakaCoherentTransformExtension.geoTransformAlong_E_eq_of_E_eq hInitial,
    localPaddedHistory_boundaryReadout (A.openSet i) O Mi hi
      (A.prefixTower i) (A.tail i) (hT i),
    localPaddedHistory_boundaryReadout (A.openSet j) O Mj hj
      (A.prefixTower j) (A.tail j) (hT j)] at h
  exact (Set.ext_iff.mp h z).symm

/-- Literal full-history length gives a real local finite cutoff. It does
not count nonempty members and need not be uniform on the atlas. -/
theorem localBoundaryReadout_eq_empty {J : Type u} (A : ActualEndpointHistories X J)
    (E : List (Set X)) (i : J) (k : ℕ)
    (hk : E.length+((A.prefixTower i).append (A.tail i)).length≤k) :
    localBoundaryReadout A E i k=∅ := by
  apply boundaryReadout_geoTransformAlong_eq_empty
  simpa only [geometricTemplate,List.length_map] using hk

/-- Each original position is the actual SAME original strict set. No
distinct-member quotient or nonempty-position reindexing occurs. -/
theorem localBoundaryReadout_original {J : Type u} (A : ActualEndpointHistories X J)
    (E : List (Set X)) (i : J) (k : Fin E.length) :
    localBoundaryReadout A E i k=localStrictSet A (E.get k) i := by
  let M := geometricTemplate (X := CMfd.of (n := n) (A.openSet i))
    univ (E.map ((Subtype.val : A.openSet i → X) ⁻¹' ·))
  let T := (A.prefixTower i).append (A.tail i)
  let k' : Fin M.E.length := ⟨k,by simpa only [M,geometricTemplate,List.length_map] using k.isLt⟩
  let kT := Fin.castLE (MemberInterTowerAlong.length_E_le_length_E_geoTransformAlong M T) k'
  change (geoTransformAlong M T).E.getD kT ∅=strictAlong T ((Subtype.val : A.openSet i → X) ⁻¹' E.get k)
  rw [List.getD_eq_get _ _ kT]
  simpa only [M,geometricTemplate,kT,k',List.get_eq_getElem,List.getElem_map,Fin.eta] using
    MemberInterTowerAlong.get_E_geoTransformAlong M T k'

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)

/-- ONLY original curve geometry and its actual retained original TEST
supply the full ambient-template TEST and literal whole-boundary SNC. -/
theorem original_localBoundary_ambient_geometry (i : X) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let M := geometricTemplate (univ : Set (A.openSet i)) (E.map ((Subtype.val : A.openSet i → X) ⁻¹' ·))
    IsGeoTestTower M ((A.prefixTower i).append (A.tail i)) ∧
      IsSNCDivisor n (geoTransformAlong M ((A.prefixTower i).append (A.tail i))).E := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let U := A.openSet i
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  obtain ⟨π,hπ,_hFirst,_hPB,_hSteps,hTest,_hZ,_hD,_hProper,_hDom,_hSNC,_hTrans,_hIso⟩ :=
    originalEndpointHistories_geometric_dictionary hn hW hE hdense hr i
  have hWU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW U
  have hEU := isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hrU : ∀ y ∈ WU,RegularAtDim (n := n) WU y 1 :=
    fun y hy => AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hr y.val hy)
  have hDenseU : WU ⊆ closure (WU \ ⋃ H ∈ EU,H) := by
    intro y hy
    have hp : y∈(Subtype.val : U → X) ⁻¹' closure (W \ ⋃ H ∈ E,H) := hdense hy
    erw [(U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
      continuous_subtype_val (W \ ⋃ H ∈ E,H)] at hp
    convert hp using 1
    congr 1
    ext z
    simp [WU,EU]
  exact (original_curve_history_full_ambient_boundary hn hWU hEU hDenseU hrU
    ((A.prefixTower i).append (A.tail i)) hTest).2

/-- ONLY original data supply the actual ambient TESTs BEFORE the OLD
chosen comparison transports ALL natural-number boundary positions. -/
theorem original_comparison_localBoundaryReadout (i j : X) (k : ℕ)
    (z : localEndpoint ((originalEndpointHistories hn hW hE hdense hr).openSet i)
      ((originalEndpointHistories hn hW hE hdense hr).openSet i⊓
        (originalEndpointHistories hn hW hE hdense hr).openSet j)
      ((originalEndpointHistories hn hW hE hdense hr).prefixTower i)
      ((originalEndpointHistories hn hW hE hdense hr).tail i)) :
    ((originalEndpointHistories hn hW hE hdense hr).comparison i j z).val∈
        localBoundaryReadout (originalEndpointHistories hn hW hE hdense hr) E j k ↔
      z.val∈localBoundaryReadout (originalEndpointHistories hn hW hE hdense hr) E i k :=
  comparison_localBoundaryReadout _ E hE
    (fun t => (original_localBoundary_ambient_geometry hn hW hE hdense hr t).1) i j k z

theorem original_transition_localBoundaryReadout (i j : X) (k : ℕ)
    (z : overlapOpen (originalEndpointHistories hn hW hE hdense hr) i j) :
    (transition (originalEndpointHistories hn hW hE hdense hr) i j z).val∈
        localBoundaryReadout (originalEndpointHistories hn hW hE hdense hr) E j k ↔
      z.val∈localBoundaryReadout (originalEndpointHistories hn hW hE hdense hr) E i k :=
  original_comparison_localBoundaryReadout hn hW hE hdense hr i j k
    (opensCongr (endpointOverlapOpen_eq_pair
      ((originalEndpointHistories hn hW hE hdense hr).openSet i)
      ((originalEndpointHistories hn hW hE hdense hr).openSet j)
      ((originalEndpointHistories hn hW hE hdense hr).prefixTower i)
      ((originalEndpointHistories hn hW hE hdense hr).tail i)) z)

/-- Every actual local readout is genuinely CLOSED, including all real
EMPTY births and every natural-number position beyond the local cutoff. -/
theorem original_localBoundaryReadout_isClosed (i : X) (k : ℕ) :
    IsClosed (localBoundaryReadout (originalEndpointHistories hn hW hE hdense hr) E i k) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let M := geometricTemplate (X := CMfd.of (n := n) (A.openSet i))
    univ (E.map ((Subtype.val : A.openSet i → X) ⁻¹' ·))
  let T := (A.prefixTower i).append (A.tail i)
  have hs := (original_localBoundary_ambient_geometry hn hW hE hdense hr i).2
  change IsClosed ((geoTransformAlong M T).E.getD k ∅)
  by_cases hk : k<(geoTransformAlong M T).E.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact hs.1 _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hk)]
    exact isClosed_empty

end OriginalInput

end
end Hironaka.HironakaSharpActualCurveBirthBoundaryOverlaps
