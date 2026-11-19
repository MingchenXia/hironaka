import Hironaka.Resolution.HironakaActualProcessedSharpCleanup
import Hironaka.Resolution.HironakaG4ZeroMaskSameGammaHistory
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4NativeProcessedMaskReindex
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings HomogenizedGlueingTower DivisorExponentAlong MonomialPartAlong GermIdealOrder
  RestrictedIdealExtension RelativePrincipalizationSpan
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalProductTraceOrder
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaActualProcessedMaskFiniteBlock HironakaActualProcessedMaskControlledSum
  HironakaG4ZeroMaskSameGammaHistory HironakaActualProcessedSharpCleanup
  HironakaG4ProcessedSupportHighCountStep
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The native mark-one SUM is the literal local span of the selected rows. -/
def nativeMaskMarked (N : Set Y) (old born : List (Set Y))
    (P : Finset (Fin old.length)) : MarkedIdeal n Y :=
  ⟨N,born,⟨fun x g => IsInSpanAt (n := n)
    (fun f => ∃ i ∈ P,(oldMonomialPart N old born i).mem x f) x g⟩,1⟩

/-- An arbitrary literal native row-mask SUM is the same marked ideal as
the processed original-row mask after the true old-row equivalence. -/
theorem native_processed_mask_eq {W : Set X} (E : List (Set X)) (T : BlowupTower X Y)
    (P' : Finset (Fin (E.map (strictAlong T)).length)) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let N := strictAlong T W
    let O := E.map (strictAlong T)
    let L := A.E
    let e := oldEquiv E T
    let P := P'.map e.symm.toEmbedding
    let M' : MarkedIdeal n Y := nativeMaskMarked N O L P' 
    P.card=P'.card ∧ processedMaskMarked W E T P=M' := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let N := strictAlong T W
  let O := E.map (strictAlong T)
  let L := A.E
  let e := oldEquiv E T
  let P := P'.map e.symm.toEmbedding
  let D := oldMonomialPart N O L
  let Sigma : GermIdeal n Y := ⟨fun x g => IsInSpanAt (n := n)
    (fun f => ∃ i ∈ P',(D i).mem x f) x g⟩
  let M' : MarkedIdeal n Y := nativeMaskMarked N O L P' 
  let M := processedMaskMarked W E T P
  change P.card=P'.card ∧ M=M'
  have hNid : A.N=N := N_geoTransformAlong _ _
  have hD (i : Fin E.length) : D (e i)=oldFactor W E T i := by
    change oldMonomialPart N O L (e i) = _
    rw [show oldFactor W E T i=monomialPartAlong n N
      (restrictOn n N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) L by
        change monomialPartAlong n A.N (restrictOn n A.N
          (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E = _
        rw [hNid]]
    exact monomial_oldEquiv N E L T i
  have hP' : P.map e.toEmbedding=P' := by simp [P,Finset.map_map]
  have hSigma : Sigma=M.ideal := by
    have h := finite_sum_oldEquiv E T P D
    rw [hP'] at h
    change Sigma=(⟨fun x g => IsInSpanAt (n := n)
      (fun f => ∃ i ∈ P,(oldFactor W E T i).mem x f) x g⟩ : GermIdeal n Y)
    rw [show Sigma=(⟨fun x g => IsInSpanAt (n := n)
      (fun f => ∃ i ∈ P,(D (e i)).mem x f) x g⟩ : GermIdeal n Y) from h]
    ext x g
    have hGen : (fun f => ∃ i ∈ P,(D (e i)).mem x f)=
        (fun f => ∃ i ∈ P,(oldFactor W E T i).mem x f) := by
      funext f
      apply propext
      constructor <;> rintro ⟨i,hi,hf⟩
      · exact ⟨i,hi,(hD i) ▸ hf⟩
      · exact ⟨i,hi,(hD i).symm ▸ hf⟩
    change IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D (e i)).mem x f) x g ↔
      IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(oldFactor W E T i).mem x f) x g
    rw [hGen]
  refine ⟨by simp [P],?_⟩
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact hNid
  · rfl
  · exact hSigma.symm
  · rfl

end
end Hironaka.HironakaG4NativeProcessedMaskReindex
