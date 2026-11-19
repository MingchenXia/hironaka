import Hironaka.Resolution.HironakaG8EmptyAwareCoverDescent

/-! Empty-aware cover descent over a prescribed base biholomorphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8EmptyAwareCoverBaseChange

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism MarkedIdealTowerTransport HironakaG3EmptyAwareHistory
  HironakaG8OccupiedSlotComparison HironakaG8EmptyAwareCoverDescent
  HironakaSharpActualCurveComparisonRestriction

variable {n : ℕ} {X X' Y Z : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- Local comparisons over literal preimage opens use the prescribed
global endpoint on their underlying points. -/
def LocalEmptyComparisonOver
    (f : X ≃ₘ⟮𝓘c,𝓘c⟯ X') (S : BlowupTower X Y) (T : BlowupTower X' Z)
    (e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z) (U : Opens X') : Prop :=
  ∃ eU : CMfd.of (n := n) (openPreimage S (preimageOpen f U)) ≃ₘ⟮𝓘c,𝓘c⟯
        CMfd.of (n := n) (openPreimage T U),
    (∀ z, (eU z).val = e z.val) ∧
    EmptyAwareTowerIso (openRestriction f (preimageOpen f U) U rfl)
      (restrict (preimageOpen f U) S) (restrict U T) eU

/-- Relative ordered footprint agreement and local literal comparisons
descend to the prescribed global base and endpoint maps. -/
theorem emptyAware_over_of_local_of_occupiedFootprints_eq
    {I : Type*} (U : I → Opens X') (hU : ∀ x : X', ∃ i, x ∈ U i)
    (f : X ≃ₘ⟮𝓘c,𝓘c⟯ X') (S : BlowupTower X Y) (T : BlowupTower X' Z)
    (e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z)
    (he : ∀ z, T.proj (e z) = f (S.proj z))
    (M : MarkedIdeals.MarkedIdeal n X) (hM : M.IsWellFormed)
    (hFoot : occupiedFootprints S = (occupiedFootprints T).map (f ⁻¹' ·))
    (hLocal : ∀ i, LocalEmptyComparisonOver f S T e (U i)) :
    EmptyAwareTowerIso f S T e := by
  let R := (transport f T).tower
  let b := (transport f T).back
  let g := e.trans b.symm
  have hB : IsTowerIso f R T b := transport_isTowerIso f T
  have hg (z : Y) : R.proj (g z) = S.proj z := by
    apply f.injective
    calc
      f (R.proj (g z)) = T.proj (b (g z)) := hB.proj_comm _
      _ = T.proj (e z) := congrArg T.proj (b.apply_symm_apply _)
      _ = f (S.proj z) := he z
  have hSR : occupiedFootprints S = occupiedFootprints R :=
    hFoot.trans (occupiedFootprints_emptyAware (emptyAware_of_isTowerIso hB)).symm
  have hLocalR (i : I) : LocalEmptyComparison S R g (preimageOpen f (U i)) := by
    obtain ⟨a,ha,hA⟩ := hLocal i
    let bU := openRestriction b (openPreimage R (preimageOpen f (U i))) (openPreimage T (U i))
      (openPreimage_eq_preimage hB (U i))
    have hBU : EmptyAwareTowerIso (openRestriction f (preimageOpen f (U i)) (U i) rfl)
        (restrict (preimageOpen f (U i)) R) (restrict (U i) T) bU :=
      emptyAware_of_isTowerIso (HironakaSharpActualCurveComparisonRestriction.IsTowerIso.open_restriction hB (U i))
    let gU := a.trans bU.symm
    have hComp := G3UniverseEmptyAwareCore.trans hA (G3UniverseEmptyAwareCore.symm hBU)
    have hBase : (openRestriction f (preimageOpen f (U i)) (U i) rfl).trans
          (openRestriction f (preimageOpen f (U i)) (U i) rfl).symm =
        Diffeomorph.refl 𝓘c (CMfd.of (n := n) (preimageOpen f (U i))) ∞ := by
      ext x
      exact congrArg Subtype.val ((openRestriction f (preimageOpen f (U i)) (U i) rfl).symm_apply_apply x)
    refine ⟨gU,fun z => ?_,hBase ▸ hComp⟩
    apply b.injective
    have h := congrArg Subtype.val (bU.apply_symm_apply (a z))
    change b (gU z).val = (a z).val at h
    rw [ha z] at h
    change b (gU z).val = b (b.symm (e z.val))
    rw [b.apply_symm_apply]
    exact h
  have hG := emptyAware_of_local_of_occupiedFootprints_eq
    (fun i => preimageOpen f (U i)) (fun x => hU (f x)) S R g hg M hM hSR hLocalR
  have hComp := G3UniverseEmptyAwareCore.trans hG (emptyAware_of_isTowerIso hB)
  have hBase : (Diffeomorph.refl 𝓘c X ∞).trans f = f := by ext x; rfl
  have hEnd : g.trans b = e := by
    ext z
    change b (b.symm (e z)) = e z
    exact b.apply_symm_apply _
  rwa [hBase,hEnd] at hComp

end Hironaka.HironakaG8EmptyAwareCoverBaseChange
