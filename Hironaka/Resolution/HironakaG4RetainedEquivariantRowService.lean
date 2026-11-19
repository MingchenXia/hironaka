import Hironaka.Resolution.HironakaG4RetainedPreparedFold
import Hironaka.Resolution.HironakaG4RetainedLowerEquivariance
import Hironaka.Resolution.HironakaG4RetainedEquivariantTailProtection
import Hironaka.Resolution.HironakaG34ExtensionEquivariance
import Hironaka.Resolution.HironakaG4GeneralSharpBadLocus

/-! A full equivariant compact-relative lower service supplies the next
protected actual row and the subsequent restored true distinct defect. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedEquivariantRowService
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals.MarkedIdeal HomogenizedGlueingTower
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  RegularPointDimension AnalyticIrreducibleComponents
  HironakaG4PreparedCentreCoordinates HironakaG4ResidualInductionInputs
  HironakaG4OrderedRetainedDefectTrace HironakaG4RetainedPreparedLocalSupport
  HironakaG4RetainedRelativeLowerService HironakaG4SharpTerminalAtlas
  HironakaG4RetainedPreparedContinuation HironakaG4RetainedPreparedFold
  HironakaG4RetainedPreparationTrace HironakaG4RetainedPreparationLowerHistory
  HironakaG4RetainedCurrentStamp HironakaG4RetainedLowerEquivariance
  HironakaG4RetainedEquivariantTailProtection HironakaG34ExtensionEquivariance
  HironakaG34MaskFoldEquivariance HironakaActualProcessedAllMasksDrop
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4GeneralSharpBadLocus RestrictEmptyTower

/-- Strictly equivariant sharp cleanup for smooth carriers with local dimensions
bounded by `d`, near every compact enclosure. -/
def CompactRelativeEquivariantSharpCleanupsExist (n d : ℕ) : Prop :=
  ∀ (X : CMfd.{u} n) (W : Set X) (E : List (Set X)),
    IsClosedSubmanifold n W → IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E,H) →
    (∀ x ∈ W,∃ e ≤ d,RegularAtDim (n := n) W x e) →
    ∀ (K : Set X), IsCompact K →
      ∃ U : Opens X, K ⊆ U ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        let u := (Subtype.val : U → X)
        IsSharpTerminalTower (u ⁻¹' W) (E.map (u ⁻¹' ·)) T ∧
        IsEquivariant (u ⁻¹' W) (E.map (u ⁻¹' ·)) T

/-- Certified sharp cleanup returns the chosen history on the same actual tower. -/
def CompactRelativeEquivariantSharpCleanupsExistUsing {n : ℕ} (lower : SharpHistoryPredicate.{u} n) (d : ℕ) : Prop :=
  ∀ (X : CMfd.{u} n) (W : Set X) (E : List (Set X)),
    IsClosedSubmanifold n W → IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E,H) →
    (∀ x ∈ W,∃ e ≤ d,RegularAtDim (n := n) W x e) →
    ∀ (K : Set X), IsCompact K →
      ∃ U : Opens X, K ⊆ U ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        let u := (Subtype.val : U → X)
        IsSharpTerminalTower (u ⁻¹' W) (E.map (u ⁻¹' ·)) T ∧
        IsEquivariant (u ⁻¹' W) (E.map (u ⁻¹' ·)) T ∧
        lower (u ⁻¹' W) (E.map (u ⁻¹' ·)) T

theorem CompactRelativeEquivariantSharpCleanupsExistUsing.forget {n d : ℕ}
    {lower : SharpHistoryPredicate.{u} n} (h : CompactRelativeEquivariantSharpCleanupsExistUsing lower d) :
    CompactRelativeEquivariantSharpCleanupsExist.{u} n d := by
  intro X W E hW hE hDense hDim K hK
  obtain ⟨U,hKU,Y,T,hEnd,hEq,_⟩ := h X W E hW hE hDense hDim K hK
  exact ⟨U,hKU,Y,T,hEnd,hEq⟩

theorem CompactRelativeEquivariantSharpCleanupsExist.usingUnrestricted {n d : ℕ}
    (h : CompactRelativeEquivariantSharpCleanupsExist.{u} n d) :
    CompactRelativeEquivariantSharpCleanupsExistUsing.{u} (n := n) (fun {_ _} _ _ _ => True) d := by
  intro X W E hW hE hDense hDim K hK
  obtain ⟨U,hKU,Y,T,hEnd,hEq⟩ := h X W E hW hE hDense hDim K hK
  exact ⟨U,hKU,Y,T,hEnd,hEq,trivial⟩

/-- The zero-dimensional carrier needs only the empty actual history. -/
theorem compactRelativeEquivariantSharpCleanupsExist_zero_using {n : ℕ}
    (lower : SharpHistoryPredicate.{u} n)
    (hRefl : ∀ (X : CMfd.{u} n) (W : Set X) (E : List (Set X)),IsClosedSubmanifold n W →
      IsSharpTerminalTower W E (.refl : BlowupTower X X) → lower W E (.refl : BlowupTower X X)) :
    CompactRelativeEquivariantSharpCleanupsExistUsing lower 0 := by
  intro X W E hW hE hDense hDim K hK
  let U : Opens X := ⊤
  let u := (Subtype.val : U → X)
  let XU := CMfd.of (n := n) U
  let NU := u ⁻¹' W
  let EU := E.map (u ⁻¹' ·)
  have gU : NativeRetainedGeometry (X := XU) NU EU [] :=
    (show NativeRetainedGeometry W E [] from
      ⟨hW,by simpa using hE,isTransverse_nil_of_isClosedSubmanifold hW,
        by simpa using hDense⟩).restrict U
  have hZero (x : U) (hx : x ∈ NU) : RegularAtDim (n := n) (M := XU) NU x 0 := by
    obtain ⟨d,hd,h⟩ := hDim x.val hx
    obtain rfl : d = 0 := Nat.eq_zero_of_le_zero hd
    exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr h
  have hBad := originalSharpBadLocus_eq_empty_of_regular_zero (X := XU) gU.carrier
    (by simpa using gU.full) (by simpa using gU.dense) hZero
  have hTerm : IsSharpTerminalTower NU EU (.refl : BlowupTower XU XU) := by
    refine ⟨trivial,trivial,trivial,?_⟩
    change HasNormalCrossings n NU EU
    intro x hx
    by_contra hNC
    have hm : x ∈ originalSharpBadLocus (n := n) NU EU := ⟨hx,hNC⟩
    rw [hBad] at hm
    exact hm
  exact ⟨U,by simp [U],XU,.refl,hTerm,isEquivariant_refl (X := XU) NU EU,hRefl XU NU EU gU.carrier hTerm⟩

theorem compactRelativeEquivariantSharpCleanupsExist_zero (n : ℕ) :
    CompactRelativeEquivariantSharpCleanupsExist.{u} n 0 :=
  (compactRelativeEquivariantSharpCleanupsExist_zero_using (n := n)
    (fun {_ _} _ _ _ => True) (fun _ _ _ _ _ => trivial)).forget

variable {n : ℕ}

set_option maxHeartbeats 1200000 in
/-- One actual lower terminal history prepares the selected row and
protects every earlier row. A strict actual retained-defect phase restores
the true distinct defect near the same compact enclosure. -/
theorem compactRelativeRetainedRowServicesExist_of_equivariant_lower_using
    (lower : SharpHistoryPredicate.{u} n) (hn : 0 < n) (d : ℕ)
    (hLower : CompactRelativeEquivariantSharpCleanupsExistUsing lower d) :
    CompactRelativeRetainedRowServicesExistUsing lower (d+1) true := by
  intro X N old born g hDim hEmpty i P hi hPrep K hK
  let L := N ∩ (oldResidualPart N old born i).zeroLocus
  let F := remainingBoundary old born i
  obtain ⟨hL,hF,hLD,hPoint⟩ := retained_selected_lower_geometry hn g hEmpty i
  have hDimL : ∀ x ∈ L,∃ e ≤ d,RegularAtDim (n := n) L x e := by
    intro x hx
    obtain ⟨e,hNe,hLe⟩ := hPoint x hx
    obtain ⟨m,hm,hNm⟩ := hDim x hx.1
    have h : e+1=m := eq_of_regularAtDim hNe hNm
    exact ⟨e,by omega,hLe⟩
  obtain ⟨U,hKU,Y,T,hTerminal,hEqLower,hChosen⟩ := hLower X L F hL hF hLD hDimL K hK
  let XU := CMfd.of (n := n) U
  let u := (Subtype.val : U → X)
  let NU := u ⁻¹' N
  let OU := old.map (u ⁻¹' ·)
  let BU := born.map (u ⁻¹' ·)
  let e : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
  let j := e i
  let LU := NU ∩ (oldResidualPart (X := XU) NU OU BU j).zeroLocus
  let FU := remainingBoundary (X := XU) OU BU j
  let P' := P.map e.toEmbedding
  have gU : NativeRetainedGeometry (X := XU) NU OU BU := g.restrict U
  obtain ⟨hLU,hFU⟩ := retained_selected_lower_tuple_open hn g i U
  change LU = u ⁻¹' L at hLU
  change FU = F.map (u ⁻¹' ·) at hFU
  change IsSharpTerminalTower (u ⁻¹' L) (F.map (u ⁻¹' ·)) T at hTerminal
  change IsEquivariant (u ⁻¹' L) (F.map (u ⁻¹' ·)) T at hEqLower
  change lower (X := XU) (Y := Y) (u ⁻¹' L) (F.map (u ⁻¹' ·)) T at hChosen
  rw [←hLU,←hFU] at hTerminal hEqLower hChosen
  have hEmptyU : actualFamilyDistinctDefect NU (oldResidualPart (X := XU) NU OU BU) = ∅ := by
    rw [(actual_retained_defect_and_rank_open hn g.carrier g.full g.born_transverse g.dense U).1,
      hEmpty,Set.preimage_empty]
  obtain ⟨hT,hFull,hSharp,hLow,hOver,hSelected,_hSupport,_hVac⟩ :=
    actual_retained_selected_row_of_lower_terminal hn gU hEmptyU j ∅ T hTerminal (by simp)
  have hEq := isEquivariant_upper_of_retained_selected_lower hn gU j T hEqLower
  have hj : j ∉ P' := by
    intro h
    obtain ⟨l,hl,hle⟩ := Finset.mem_map.mp h
    exact hi ((e.injective hle) ▸ hl)
  have hPrepU : ∀ l ∈ P',RetainedRowPrepared NU OU BU l (.refl : BlowupTower XU XU) := by
    intro l hl
    obtain ⟨m,hm,rfl⟩ := Finset.mem_map.mp hl
    exact (retained_prepared_row_restrict_open hn g.carrier g.full
      g.born_transverse g.dense m (hPrep m hm) U).1
  have hFsub : FU.Sublist (OU ++ BU) := (List.eraseIdx_sublist OU j.val).append (List.Sublist.refl BU)
  have hEqProtection : IsEquivariant LU (OU ++ BU) T :=
    isEquivariant_mono (fun _ hH => hFsub.subset hH) hEqLower
  have hOverTop : CentresOver ((⊤ : Opens XU) : Set XU) T :=
    centresOver_mono_local (subset_univ _) T hOver
  have hLUClosed : IsClosed LU := (retained_selected_lower_geometry hn gU hEmptyU j).1.1
  have hPrior := retained_mixed_tail_protects_prepared_rows_with_window hn gU P' j hj hPrepU
    (geometricTemplate LU FU) hLUClosed rfl ⊤ [] (by simp) T hLow hOverTop
    (by change IsEquivariant (X := XU) LU (OU ++ BU) T; exact hEqProtection) hT hFull
  apply exists_prepared_retained_defect_rerun_after_near_using lower hn g hK U hKU T (insert i P) true [.lower i.val] hT hFull hSharp
    (fun _ => ⟨hEq,RetainedPreparationTrace.lower gU hEmptyU j hTerminal hEqLower,hChosen⟩)
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl | hk
  · exact hSelected
  · exact (hPrior (e k) (Finset.mem_map.mpr ⟨k,hk,rfl⟩)).1

/-- Lower cleanup may be used without specifying a smaller-dimensional history family. -/
theorem compactRelativeRetainedRowServicesExist_of_equivariant_lower (hn : 0 < n) (d : ℕ)
    (hLower : CompactRelativeEquivariantSharpCleanupsExist.{u} n d) :
    CompactRelativeRetainedRowServicesExist.{u} n (d+1) true := by
  intro X N old born g hDim hEmpty i P hi hPrep K hK
  exact (compactRelativeRetainedRowServicesExist_of_equivariant_lower_using (fun {_ _} _ _ _ => True)
    hn d hLower.usingUnrestricted X N old born g hDim hEmpty i P hi hPrep K hK).forget

end
end Hironaka.HironakaG4RetainedEquivariantRowService
