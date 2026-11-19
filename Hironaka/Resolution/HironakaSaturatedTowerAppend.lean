import Hironaka.Resolution.HironakaG10FlatProperShrinking
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Resolution.HironakaNormalCrossingsOpenRestrictionSeparation
import Hironaka.Resolution.HironakaNormalCrossingsSeparationChoiceComparison

/-! Saturated open restriction of a literal ambient prefix and a supplied
suffix. This geometry is independent of the marked records on the towers. -/

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.HironakaSaturatedTowerAppend

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdealTowerTransport MaxLocusLocal HomogenizedGlueingTower
  HironakaNormalCrossingsSeparationChoiceComparison HironakaNormalCrossingsOpenRestrictionSeparation

/-- After saturating the base open, the actual restricted prefix and
transported restricted suffix concatenate, with an exact endpoint open,
projection square and both strict-transform identities. -/
theorem exists_saturated_tower_append {n : ℕ} {X Y : CMfd.{u} n}
    (T : BlowupTower X Y) (K : Set X) (V : Opens Y) (hKV : T.proj ⁻¹' K ⊆ V)
    {Z : CMfd.{u} n} (S : BlowupTower (CMfd.of (n := n) V) Z) :
    ∃ (O : Opens X), K ⊆ O ∧ ∃ (hOV : openPreimage T O ≤ V),
      let U := openPreimage T O
      let D := nestedOpens V U
      let e := (nestedOpensDiffeo (n := n) hOV).symm
      let tail := transport e (restrict D S)
      let A := (restrict O T).append tail.tower
      let b : tail.target → Z := fun z => (tail.back z).val
      IsTowerIso e tail.tower (restrict D S) tail.back ∧
      (∀ z, ((tail.tower.proj z : U) : Y) = (S.proj (b z)).val) ∧
      (∀ z, (A.proj z).val = T.proj (S.proj (b z)).val) ∧
      Set.range b = (fun z => T.proj (S.proj z).val) ⁻¹' (O : Set X) ∧
      (∀ W : Set X, strictAlong A ((Subtype.val : O → X) ⁻¹' W) =
        b ⁻¹' strictAlong S ((Subtype.val : V → Y) ⁻¹' strictAlong T W)) ∧
      (∀ W : Set X, strictTransform n A.proj ((Subtype.val : O → X) ⁻¹' W) =
        b ⁻¹' strictTransform n S.proj ((Subtype.val : V → Y) ⁻¹' strictTransform n T.proj W)) := by
  obtain ⟨O₀, hOpen, hKO, hSat⟩ := HironakaG10FlatProperShrinking.exists_open_nhds_preimage_subset
    (HironakaLocalPrincipalization.isProperMap_proj T).isClosedMap V.isOpen hKV
  let O : Opens X := ⟨O₀, hOpen⟩
  have hOV : openPreimage T O ≤ V := hSat
  let U := openPreimage T O
  let D := nestedOpens V U
  let e := (nestedOpensDiffeo (n := n) hOV).symm
  let L := restrict O T
  let R := restrict D S
  let tail := transport e R
  let A := L.append tail.tower
  let b : tail.target → Z := fun z => (tail.back z).val
  have hIso : IsTowerIso e tail.tower R tail.back := transport_isTowerIso e R
  have hProj (z : tail.target) : ((tail.tower.proj z : U) : Y) = (S.proj (b z)).val := by
    have hp := congrArg (fun q : D => q.val.val) (proj_transport e R z)
    change ((tail.tower.proj z : U) : Y) = ((R.proj (tail.back z)).val : Y) at hp
    simpa only [R, proj_restrict, b] using hp
  refine ⟨O, hKO, hOV, hIso, hProj, ?_, ?_, ?_, ?_⟩
  · intro z
    simpa only [A, L, BlowupTower.proj_append, Function.comp_apply, proj_restrict] using
      congrArg T.proj (hProj z)
  · ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact (tail.back q).property
    · intro hz
      let p : openPreimage S D := ⟨z, hz⟩
      refine ⟨tail.back.symm p, ?_⟩
      change (tail.back (tail.back.symm p)).val = z
      rw [tail.back.apply_symm_apply]
  · intro W
    let WV := (Subtype.val : V → Y) ⁻¹' strictAlong T W
    have hCarrier : strictAlong L ((Subtype.val : O → X) ⁻¹' W) =
        e ⁻¹' ((Subtype.val : D → V) ⁻¹' WV) := strictAlong_restrict O T W
    change strictAlong A ((Subtype.val : O → X) ⁻¹' W) = b ⁻¹' strictAlong S WV
    rw [MemberInterLocusAlong.strictAlong_append, hCarrier, strictAlong_transport,
      strictAlong_restrict D S WV]
    rfl
  · intro W
    let WV := (Subtype.val : V → Y) ⁻¹' strictTransform n T.proj W
    have hCarrier : strictTransform n L.proj ((Subtype.val : O → X) ⁻¹' W) =
        e ⁻¹' ((Subtype.val : D → V) ⁻¹' WV) := strictTransform_restricted_tower O T W
    have h := strictTransform_preimage_of_square e tail.back tail.tower.contMDiff_proj
        R.contMDiff_proj ((Subtype.val : D → V) ⁻¹' WV)
        (isClosed_closure.preimage (continuous_subtype_val.comp continuous_subtype_val))
        (fun z => (proj_transport e R z).symm)
    rw [← hCarrier, strictTransform_restricted_tower D S WV] at h
    change strictTransform n A.proj ((Subtype.val : O → X) ⁻¹' W) = b ⁻¹' strictTransform n S.proj WV
    rw [BlowupTower.proj_append,
      StrictTransformComposition.strictTransform_comp L.contMDiff_proj tail.tower.contMDiff_proj]
    exact h

end
end Hironaka.HironakaSaturatedTowerAppend
