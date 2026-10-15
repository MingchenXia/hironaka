/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualMixedCentreWholeStrictTraceGeometry

/-! Genuine whole open pullback and full original germ dictionaries for the
actual ambient strict-trace residual. No chronological identification is assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualStrictTraceOpenNonmonomial
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualMixedCentreWholeStrictTraceGeometry HironakaSharpActualDiscreteCentreMemberLocalBranch
  HironakaSharpActualChronologicalStrictStep RelativePrincipalizationSpan RestrictedIdealExtension
  MarkedIdealRestrictOpen MonomialPartAlong DivisorExponentAlong NormalCrossings
  DerivativeIdealAlongEtale MarkedIdeals MarkedIdeals.MarkedIdeal NonmonomialTransformAlong
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- True whole normalized vanishing ideals retain their actual open pullback,
before greatest-factor parts are compared. -/
theorem actual_normalized_trace_whole_open_pullback {N H : Set X}
    (hN : IsClosedSubmanifold n N) (hH : IsClosedSubmanifold n H) (U : Opens X) :
    restrictOn n ((Subtype.val : U → X) ⁻¹' N)
      (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))=
      GermIdeal.pullback (m := n) (Subtype.val : U → X)
        (restrictOn n N (vanishingIdeal (n := n) H)) := by
  have hcI := isCoherent_restrictOn (VanishingIdealCoherent.isCoherent_vanishingIdeal hH)
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)
  ext x g
  exact (actual_normalized_vanishing_open_germ_iff hH U x g).trans
    (mem_pullback_val_iff U hcI).symm

/-- Actual geometry internally supplies BOTH part coherences before the genuine
whole open Nm theorem gives EVERY actual extended-germ direction. -/
theorem actual_nonmonomial_open_germ_iff (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    (U : Opens X) (x : U) (g : U → ℂ) :
    (nonmonomialPartAlong n ((Subtype.val : U → X) ⁻¹' N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) I)
      (E.map ((Subtype.val : U → X) ⁻¹' ·))).mem x g ↔
        (nonmonomialPartAlong n N I E).mem x.val (extendOpens U g) := by
  have hcM := isCoherent_monomialPartAlong hn hN hE hT hI hnz
  have hcR := isCoherent_nonmonomialPartAlong hn hN hE hT hI hnz
  have hEq := MonomialPartEtale.pullback_nonmonomialPartAlong
    (fun y : U => ⟨openInv U y,isLocalInverseAt_val U y⟩) hI hcM hcR
  rw [←hEq]
  exact mem_pullback_val_iff U hcR

/-- ONLY original mixed discrete-centre geometry supplies the true next trace
and part geometry before BOTH full open germ directions on EVERY real open. -/
theorem actual_mixed_discrete_strict_trace_open_nonmonomial_iff (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H))
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    (V : Opens Y) (z : V) (g : V → ℂ) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let H' := BlowupStrictSubmanifold.geoStrictTransform π C H
    let I' := restrictOn n N' (vanishingIdeal (n := n) H')
    (nonmonomialPartAlong n ((Subtype.val : V → Y) ⁻¹' N')
      (restrictOn n ((Subtype.val : V → Y) ⁻¹' N')
        (vanishingIdeal (n := n) ((Subtype.val : V → Y) ⁻¹' H')))
      [(Subtype.val : V → Y) ⁻¹' (π ⁻¹' C)]).mem z g ↔
        (nonmonomialPartAlong n N' I' [π ⁻¹' C]).mem z.val (extendOpens V g) := by
  obtain ⟨hN',hAmbient,hcI,hnzI,_hDense,_hPr⟩ :=
    actual_mixed_discrete_centre_whole_strict_trace_geometry hn hN hH hdense hrC hπ hCN
  have hH' : IsClosedSubmanifold n (BlowupStrictSubmanifold.geoStrictTransform π C H) :=
    MonomialPart.isClosedSubmanifold_get hn hAmbient ⟨0,by simp⟩
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length))
  obtain ⟨hNewE,hNewT⟩ := actual_accumulated_exceptional_geometry hN hcH isSNCDivisor_nil
    (isTransverse_nil_of_isClosedSubmanifold hN) hπ hCN
    (hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1)
  have hE : IsSNCDivisor n [π ⁻¹' C] := by simpa only [List.map_nil,List.nil_append] using hNewE
  have hTrans : IsTransverse n (BlowupStrictSubmanifold.geoStrictTransform π C N) [π ⁻¹' C] := by
    change IsTransverse n (BlowupStrictSubmanifold.geoStrictTransform π C N)
      ([].map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) at hNewT
    simpa only [List.map_nil,List.nil_append] using hNewT
  have hOpen := actual_normalized_trace_whole_open_pullback hN' hH' V
  change (nonmonomialPartAlong n _ _ _).mem z g ↔ _
  rw [hOpen]
  simpa only [List.map_singleton] using actual_nonmonomial_open_germ_iff hn hN' hE hTrans hcI hnzI V z g

end
end Hironaka.HironakaSharpActualStrictTraceOpenNonmonomial
