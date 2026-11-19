import Hironaka.Resolution.HironakaG4RecordedPartsOpen
import Hironaka.Blowup.NormalCrossingsInvariance

/-! Actual old-member parts provide the normalized local chart inputs. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4WindowActualParts
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings NormalCrossingsInvariance HironakaG4PreparedCentreCoordinates
  HironakaG4RecordedPartsOpen RelativePrincipalizationSpan RestrictedIdealExtension
  MonomialPartAlong NonmonomialTransformAlong DivisorExponentAlong BlowupRestrictOpen

variable {n : ℕ} {X : CMfd.{u} n}

/-- On any source open, the actual normalized old trace is coherent and
nonzero, has the actual monomial--residual factorization, and both factors
are the pullbacks of the ambient recorded parts. -/
theorem actual_window_normalized_parts (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (U : Opens X) (i : Fin old.length) :
    let NU := (Subtype.val : U → X) ⁻¹' N
    let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    let IU := restrictOn n NU (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' old.get i))
    let DU := monomialPartAlong n NU IU bornU
    let JU := nonmonomialPartAlong n NU IU bornU
    IU.IsCoherent ∧ (∀ y ∈ NU, IsNonzeroAlongAt NU IU y) ∧
      IU = restrictOn n NU (DU.mul JU) ∧
      DU = GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldMonomialPart N old born i) ∧
      JU = GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i) := by
  let NU := (Subtype.val : U → X) ⁻¹' N
  let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let iU : Fin oldU.length := ⟨i.val, by simpa only [oldU,List.length_map] using i.isLt⟩
  have hi : oldU.get iU = (Subtype.val : U → X) ⁻¹' old.get i := by
    simp [oldU,iU,List.get_eq_getElem]
  have hNU := isClosedSubmanifold_preimage_val hN U
  have hEU : IsSNCDivisor n (oldU ++ bornU) := by
    simpa only [oldU,bornU,List.map_append] using
      isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hTrU : IsTransverse n NU bornU := isTransverse_preimage (pullsBackCoordinates_val U) hTr
  have openDensity (L : List (Set X)) (hDense : N ⊆ closure (N \ ⋃ H ∈ L,H)) :
      (Subtype.val : U → X) ⁻¹' N ⊆ closure ((Subtype.val : U → X) ⁻¹' N \
        ⋃ H ∈ L.map ((Subtype.val : U → X) ⁻¹' ·),H) := by
    intro y hy
    have hp : y ∈ (Subtype.val : U → X) ⁻¹' closure (N \ ⋃ H ∈ L,H) := hDense hy
    erw [U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (N \ ⋃ H ∈ L,H)] at hp
    convert hp using 1
    congr 1
    ext z
    simp
  have hDenseU : NU ⊆ closure (NU \ ⋃ H ∈ oldU ++ bornU,H) := by
    simpa only [NU,oldU,bornU,List.map_append] using openDensity (old ++ born) hdense
  obtain ⟨hc,hnz,_hcJ,_hnzJ,_hcD,_hnzD,_hMono,hWhole⟩ :=
    actual_old_parts_geometry (X := CMfd.of (n := n) U) hn hNU hEU hTrU hDenseU iU
  have hpull := actual_old_parts_pullback_open hn hN hE hTr hdense U i
  dsimp only at hpull ⊢
  refine ⟨?_, ?_, ?_, hpull.1, hpull.2⟩
  · simpa only [oldTraceIdeal,hi] using hc
  · simpa only [oldTraceIdeal,hi] using hnz
  · simpa only [oldTraceIdeal,oldMonomialPart,oldResidualPart,hi] using hWhole

end
end Hironaka.HironakaG4WindowActualParts
