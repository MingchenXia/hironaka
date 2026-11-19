import Hironaka.Resolution.HironakaG8CaseTHypersurfaceFrame
import Hironaka.Resolution.HironakaG8CaseTSingleCutOrder
import Hironaka.Invariant.MaxLocusLocal

/-!
# A common open with the selected boundary member removed

Two actual hypersurface-frame constructions are intersected. The remaining
ordered boundary is SNC and transverse to both literal restricted carriers.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseTCommonRemainder
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupFlatCoordinates BlowupStrictSubmanifold NormalCrossings
  NormalCrossingsInvariance GermIdealOrder HironakaBaseChange

/-- The two hypersurface frames have a common actual open on which the same
ordered remainder is SNC and transverse to both restricted carriers. -/
theorem exists_common_remainder_transverse_open
    {n m : ℕ} {X : CMfd.{u} n} {P Q NP NQ : Set X} {x : X}
    (hP : RegularAtDim (n := n) P x m) (hQ : RegularAtDim (n := n) Q x m)
    (hNP : RegularAtDim (n := n) NP x (m+1)) (hNQ : RegularAtDim (n := n) NQ x (m+1))
    (hPsub : P ⊆ NP) (hQsub : Q ⊆ NQ)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hTransP : IsTransverse n NP E) (hTransQ : IsTransverse n NQ E)
    (i : Fin E.length) (hxH : x ∈ E.get i)
    (hTP : x ∈ cosupport n P (vanishingIdeal (n := n) (E.get i)) 2)
    (hTQ : x ∈ cosupport n Q (vanishingIdeal (n := n) (E.get i)) 2) :
    ∃ U : Opens X, x ∈ U ∧
      IsSNCDivisor n ((E.eraseIdx i.val).map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U → X) ⁻¹' P)
        ((E.eraseIdx i.val).map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U → X) ⁻¹' Q)
        ((E.eraseIdx i.val).map ((Subtype.val : U → X) ⁻¹' ·)) := by
  obtain ⟨_, _, _, UP, _, _, _, _, _, _, _, hxUP, _, _, hSNCUP, hTPUP⟩ :=
    HironakaG8CaseTHypersurfaceFrame.exists_hypersurface_transverse_open
      hP hNP hPsub E hE hTransP i hxH hTP
  obtain ⟨_, _, _, UQ, _, _, _, _, _, _, _, hxUQ, _, _, _hSNCUQ, hTQUQ⟩ :=
    HironakaG8CaseTHypersurfaceFrame.exists_hypersurface_transverse_open
      hQ hNQ hQsub E hE hTransQ i hxH hTQ
  let U : Opens X := UP ⊓ UQ
  let fP : U → UP := fun z => ⟨z.val, z.property.1⟩
  let fQ : U → UQ := fun z => ⟨z.val, z.property.2⟩
  have hOpenP : IsOpenHoloEmbedding n fP :=
    ⟨MaxLocusLocal.nestedOpens UP U, (MaxLocusLocal.nestedOpensDiffeo (n := n) inf_le_left).symm, fun _ => rfl⟩
  have hOpenQ : IsOpenHoloEmbedding n fQ :=
    ⟨MaxLocusLocal.nestedOpens UQ U, (MaxLocusLocal.nestedOpensDiffeo (n := n) inf_le_right).symm, fun _ => rfl⟩
  have hs := isSNCDivisor_map_preimage hOpenP.pullsBackCoordinates hOpenP.continuous hSNCUP
  have hp := isTransverse_preimage hOpenP.pullsBackCoordinates hTPUP
  have hq := isTransverse_preimage hOpenQ.pullsBackCoordinates hTQUQ
  refine ⟨U, ⟨hxUP, hxUQ⟩, ?_, ?_, ?_⟩
  · simpa only [List.map_map, Function.comp_def, Set.preimage_preimage] using hs
  · simpa only [List.map_map, Function.comp_def, Set.preimage_preimage] using hp
  · simpa only [List.map_map, Function.comp_def, Set.preimage_preimage] using hq

end
end Hironaka.HironakaG8CaseTCommonRemainder
