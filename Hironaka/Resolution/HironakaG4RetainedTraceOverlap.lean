import Hironaka.Resolution.HironakaG4RetainedTraceComparison
import Hironaka.Resolution.HironakaG4RetainedDefectRelativeExit
import Hironaka.Resolution.HironakaG3UniversePhysicalClassComparisons

/-! Compatibility of ordered retained exits on their literal open overlaps. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedTraceOverlap
noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealTowerTransport MaxLocusLocal
  MarkedIdeals.MarkedIdeal HomogenizedGlueingTower
  G3UniverseEmptyAwareCore G3UniversePhysicalClassComparisons HironakaG3RTowerClass
  HironakaOriginalTerminalOverlapComparison
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaG4PreparedCentreCoordinates HironakaG4CompactWholeMonomialMaskPhase
  HironakaG4OrderedRetainedDefectTrace HironakaG4RetainedTraceComparison HironakaG4RetainedDefectRelativeExit

variable {n : ℕ} {X : CMfd.{u} n} {N : Set X} {old born : List (Set X)} {hn : 0 < n}

private def trace_on_literal_overlap (g : NativeRetainedGeometry N old born)
    {U W : Opens X} (hWU : W ≤ U) {Y : CMfd.{u} n}
    {T : BlowupTower (CMfd.of (n := n) U) Y} {μ : WithTop RetainedStampRank}
    (R : OrderedRetainedDefectTrace hn ((Subtype.val : U → X) ⁻¹' N)
      (old.map ((Subtype.val : U → X) ⁻¹' ·)) (born.map ((Subtype.val : U → X) ⁻¹' ·)) μ T) :
    let w := (Subtype.val : W → X)
    let e := (nestedOpensDiffeo (n := n) hWU).symm
    OrderedRetainedDefectTrace hn (w ⁻¹' N) (old.map (w ⁻¹' ·)) (born.map (w ⁻¹' ·)) μ
      (transport e (restrict (nestedOpens U W) T)).tower := by
  intro w e
  let D := nestedOpens U W
  let u := (Subtype.val : U → X)
  let d := (Subtype.val : D → U)
  let gU := g.restrict U
  have T' := (R.restrictOpen D gU).rebase e (gU.restrict D)
  have hMap (L : List (Set X)) :
      (((L.map (u ⁻¹' ·)).map (d ⁻¹' ·)).map (e ⁻¹' ·)) = L.map (w ⁻¹' ·) := by
    simp only [List.map_map]
    rfl
  rw [hMap old,hMap born] at T'
  exact T'

set_option maxHeartbeats 650000 in
/-- Two independently chosen finite retained histories compare on every
common source open by its actual nested-open base map. -/
theorem compare_ordered_retained_traces_on_overlap (g : NativeRetainedGeometry N old born)
    {U₁ U₂ W : Opens X} (h₁ : W ≤ U₁) (h₂ : W ≤ U₂)
    {Y₁ Y₂ : CMfd.{u} n} {μ₁ μ₂ : WithTop RetainedStampRank}
    {T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁}
    {T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂}
    (R₁ : OrderedRetainedDefectTrace hn ((Subtype.val : U₁ → X) ⁻¹' N)
      (old.map ((Subtype.val : U₁ → X) ⁻¹' ·)) (born.map ((Subtype.val : U₁ → X) ⁻¹' ·)) μ₁ T₁)
    (R₂ : OrderedRetainedDefectTrace hn ((Subtype.val : U₂ → X) ⁻¹' N)
      (old.map ((Subtype.val : U₂ → X) ⁻¹' ·)) (born.map ((Subtype.val : U₂ → X) ⁻¹' ·)) μ₂ T₂) :
    let D₁ := nestedOpens U₁ W
    let D₂ := nestedOpens U₂ W
    ∃ ψ : CMfd.of (n := n) (openPreimage T₁ D₁)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₂ D₂),
      EmptyAwareTowerIso (overlapBaseEquiv (n := n) h₁ h₂)
        (restrict D₁ T₁) (restrict D₂ T₂) ψ := by
  intro D₁ D₂
  let e₁ := (nestedOpensDiffeo (n := n) h₁).symm
  let e₂ := (nestedOpensDiffeo (n := n) h₂).symm
  let L₁ := restrict D₁ T₁
  let L₂ := restrict D₂ T₂
  let t₁ := transport e₁ L₁
  let t₂ := transport e₂ L₂
  let ref := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) W) ∞
  let Q₁ := trace_on_literal_overlap g h₁ R₁
  let Q₂ := trace_on_literal_overlap g h₂ R₂
  let gW := g.restrict W
  obtain ⟨χ,hχ⟩ := compare_ordered_retained_traces gW gW rfl Q₁ Q₂
  refine ⟨(t₁.back.symm.trans χ).trans t₂.back,?_⟩
  have hIso := G3UniverseEmptyAwareCore.trans
    (G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso (transport_isTowerIso e₁ L₁).symm) hχ)
    (emptyAware_of_isTowerIso (transport_isTowerIso e₂ L₂))
  have hBase : (e₁.symm.trans ref).trans e₂ = overlapBaseEquiv (n := n) h₁ h₂ :=
    Diffeomorph.ext fun _ => rfl
  rw [←hBase]
  exact hIso

/-- The finite ordered retained-defect exits as a class of actual local towers. -/
def OrderedRetainedDefectExitClass (hn : 0 < n) (N : Set X) (old born : List (Set X)) :
    LocalTowerClass X := fun U _ T =>
  let u := (Subtype.val : U → X)
  let NU := u ⁻¹' N
  let OU := old.map (u ⁻¹' ·)
  let BU := born.map (u ⁻¹' ·)
  let C := geoTransformAlong (geometricTemplate NU BU) T
  IsGeoTestTower (geometricTemplate NU BU) T ∧
  IsGeoTestTower (geometricTemplate (univ : Set U) (OU ++ BU)) T ∧
  CurrentSharpCentres NU (OU ++ BU) T ∧
  actualFamilyDistinctDefect C.N (oldResidualPart C.N (OU.map (strictAlong T)) C.E) = ∅ ∧
  Nonempty (OrderedRetainedDefectTrace hn NU OU BU ⊤ T)

/-- Finite ordered retained-defect exits cover the base and have actual
empty-aware comparisons on the whole chart overlaps. -/
theorem ordered_retained_exit_class_covers_and_compares
    (g : NativeRetainedGeometry N old born) :
    Covers (OrderedRetainedDefectExitClass hn N old born) ∧
      HasPhysicalComparisons (OrderedRetainedDefectExitClass hn N old born) := by
  constructor
  · intro x
    obtain ⟨U,hU,Y,T,hT,hFull,hSharp,hDef,hTrace⟩ :=
      exists_ordered_retained_defect_exit_near_compact hn g.carrier g.full g.born_transverse g.dense
        (isCompact_singleton (x := x))
    exact ⟨U,hU (mem_singleton x),Y,T,hT,hFull,hSharp,hDef,hTrace⟩
  · intro U₁ U₂ Y₁ Y₂ T₁ T₂ hT₁ hT₂
    obtain ⟨_,_,_,_,⟨r₁⟩⟩ := hT₁
    obtain ⟨_,_,_,_,⟨r₂⟩⟩ := hT₂
    exact compare_ordered_retained_traces_on_overlap g inf_le_left inf_le_right r₁ r₂

/-- The finite retained exits glue to the proper modification carried by
their physically compatible local histories. -/
theorem exists_glued_ordered_retained_defect_exit (g : NativeRetainedGeometry N old born) :
    ∃ (Z : CMfd.{u} n) (P : Z → X), IsGluedFrom (OrderedRetainedDefectExitClass hn N old born) Z P := by
  obtain ⟨hCover,hCompare⟩ := ordered_retained_exit_class_covers_and_compares (hn := hn) g
  exact exists_isGluedFrom hCover (physical_comparisons_to_comparisons hCompare)

end
end Hironaka.HironakaG4RetainedTraceOverlap
