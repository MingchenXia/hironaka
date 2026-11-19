import Hironaka.Resolution.HironakaG4TransverseBoundaryStrictPullback
import Hironaka.Resolution.HironakaG4PreparedCentreCoordinates
import Hironaka.Resolution.HironakaSharpActualCompositeTotalResidual
import Hironaka.Resolution.HironakaSharpActualTotalNonmonomialTransport
import Hironaka.Resolution.HironakaSharpActualTotalAccumulatedResidual

set_option autoImplicit false

/-! The actual transverse old-row residual on the SAME blowup and ALL born labels.
Source-first chapter: hironaka-g4-transverse-old-residual-step.tex.
No arbitrary-centre order-one persistence or future history is asserted. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG4TransverseOldResidualStep

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold NormalCrossings NormalCrossingsComparison
  MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaG4TransverseBoundaryStrictPullback HironakaG4PreparedCentreCoordinates
  HironakaSharpActualCompositeTotalResidual HironakaSharpActualTotalNonmonomialTransport
  HironakaSharpActualTotalAccumulatedResidual HironakaSharpActualChronologicalStrictStep
  HironakaSharpOriginalFirstMemberResidualPrincipal HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalFirstMemberExceptionalFactor HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  MonomialPartAlong NonmonomialTransformAlong GermIdealOrder DivisorExponentAlong

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- A real transverse old row has its actual chronological strict residual on
the SAME blowup and ENTIRE accumulated born list, with whole ideals retained. -/
theorem actual_transverse_old_residual_step (hn : 0 < n) {N C : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    (hCNC : HasNormalCrossings n C (old ++ born))
    (hTransOld : IsTransverse n C [old.get i]) :
    let N' := geoStrictTransform π C N
    let born' := born.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    let I' := restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform π C (old.get i)))
    I'.IsCoherent ∧ (∀ y ∈ N',IsNonzeroAlongAt N' I' y) ∧
      nonmonomialPartAlong n N' I' born'=
        nextRelativeStrict N (oldResidualPart N old born i) C π := by
  let I := oldTraceIdeal N old i
  let J := oldResidualPart N old born i
  let N' := geoStrictTransform π C N
  let born' := born.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  let I' := restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform π C (old.get i)))
  let Q := nextTotalMarked N I C π
  have hOld := isSNCDivisor_of_sublist hE (List.sublist_append_left old born)
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hSingle : IsSNCDivisor n [old.get i] := isSNCDivisor_of_sublist hOld (by simp)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hOld i)
  obtain ⟨hcI,hnzI,hcJ,hnzJ,_hcD,_hnzD,_hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  have hCborn : HasNormalCrossings n C born :=
    hasNormalCrossings_of_forall_mem hCNC fun _ h => List.mem_append_right old h
  have hN' : IsClosedSubmanifold n N' :=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hRaw : Q.ideal=restrictOn n N' (GermIdeal.pullback (m := n) π I) :=
    geoTransform_zeroMark_ideal_eq_restricted_total (⟨N,[],I,0⟩ : MarkedIdeal n X) rfl C π
  have hTrace : Q.ideal=I' := by
    rw [hRaw]
    change restrictOn n N' (GermIdeal.pullback (m := n) π
      (restrictOn n N (vanishingIdeal (n := n) (old.get i))))=I'
    rw [actual_normalized_pullback_restrictOn hN hN'.1 hcH hπ.contMDiff
      (fun _ hy => geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hy)]
    rw [pullback_vanishingIdeal_eq_strict_of_transverse hn hSingle hTransOld hπ]
  have hcQ : Q.ideal.IsCoherent :=
    isCoherent_geoTransform_ideal_without_inclusion (⟨N,[],I,0⟩ : MarkedIdeal n X)
      hN hcI hπ hCN
  have hnzQ : ∀ y ∈ N',IsNonzeroAlongAt N' Q.ideal y :=
    isNonzeroAlongAt_geoTransform_without_admissibility (⟨N,[],I,0⟩ : MarkedIdeal n X)
      hN hcI hπ hCN hnzI
  have hprJ : ∀ x ∈ N,∃ c : X → ℂ,HolomorphicAt n c x ∧
      ∀ g,J.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=c) x g := by
    intro x hx
    obtain ⟨f,hf,hF⟩ := exists_originalMember_principal hn hOld (List.get_mem old i) x
    have hIgen : ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g :=
      fun g => and_congr_right fun _ =>
        HironakaSharpOriginalMemberProduct.restricted_span_iff_principal hf hF g
    obtain ⟨_m,c,_hm,_hmD,hc,_hfc,hJgen⟩ :=
      exists_actual_relative_principal_residual hn hN hBorn hTr hcI hnzI hx f hf hIgen
    exact ⟨c,GermIdeal.IsCoherent.holomorphicAt_mem hcJ hc,hJgen⟩
  obtain ⟨_hcJ,_hcM,_hnzM,_hmM,hNoBorn,_hnzJ,_hFactor⟩ :=
    parts_hypotheses hn (⟨N,born,I,0⟩ : MarkedIdeal n X) ⟨hN,hcI,hBorn,hTr⟩ hnzI
  have hTransport := actual_whole_total_nonmonomial_parts_transport hn hN hBorn hTr
    hcI hnzI hπ hCN hCborn
  have hStrict := nextTotal_accumulated_nonmonomial_eq_nextStrict hn hN hBorn hTr
    hcJ hnzJ hprJ hπ hCN hCborn hNoBorn
  change nonmonomialPartAlong n N' Q.ideal born'=
    nonmonomialPartAlong n N' (nextTotalMarked N J C π).ideal born' at hTransport
  change nonmonomialPartAlong n N' (nextTotalMarked N J C π).ideal born'=
    nextRelativeStrict N J C π at hStrict
  change I'.IsCoherent ∧ (∀ y ∈ N',IsNonzeroAlongAt N' I' y) ∧
    nonmonomialPartAlong n N' I' born'=nextRelativeStrict N J C π
  refine ⟨?_,?_,?_⟩
  · rw [←hTrace]
    exact hcQ
  · intro y hy
    rw [←hTrace]
    exact hnzQ y hy
  · rw [←hTrace]
    exact hTransport.trans hStrict

end

end Hironaka.HironakaG4TransverseOldResidualStep
