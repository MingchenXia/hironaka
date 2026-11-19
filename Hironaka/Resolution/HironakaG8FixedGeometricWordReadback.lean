import Hironaka.Resolution.HironakaG8GeometricIndexedWord

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8FixedGeometricWordReadback

open BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals
  HironakaG8OccupiedSlotComparison HironakaG8IndexedDisjointSwap
  HironakaG8NestedVisibleWordLift HironakaG8GeometricIndexedWord G3UniverseEmptyAwareCore

/-- Compose the maps attached to the supplied physical path. The same
terminal map underlies every literal restricted comparison. -/
theorem fixed_geometric_word_readback {n : ℕ} {B : CMfd.{0} n}
    (W : Set B) (M : MarkedIdeal n B) (A : ℕ → Set B)
    {w : List ℕ} {L R : TowerAt B} (word : RealizedWord (GeometricIndexedMove W M) w L R)
    (σ : ℕ ≃ ℕ) (hFoot : ∀ j, slotFootprint L.2 j = A (σ j)) :
    ∃ e : L.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ R.1,
      R.2.proj ∘ e = L.2.proj ∧
      (∀ j, slotFootprint R.2 j = A (reordering σ w j)) ∧
      ∀ U : Opens B, OpenAvoidsSwapPairs U A σ w →
        ∃ χ : CMfd.of (n := n) (openPreimage L.2 U)
            ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R.2 U),
          (∀ z, (χ z).val = e z.val) ∧
          EmptyAwareTowerIso
            (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
            (restrict U L.2) (restrict U R.2) χ := by
  induction word generalizing σ with
  | nil L =>
      exact ⟨Diffeomorph.refl _ _ _, rfl, hFoot, fun U _ =>
        ⟨Diffeomorph.refl _ _ _, fun _ => rfl,
          emptyAware_of_isTowerIso (IsTowerIso.refl_self (restrict U L.2))⟩⟩
  | @cons i w L S R hMove _ ih =>
      obtain ⟨e,he,_,hOpen⟩ := hMove.2.2.2.2.2
      have hStep j : slotFootprint S.2 j = A (((Equiv.swap i (i+1)).trans σ) j) :=
        (hMove.1.2.2.2.2 j).trans (hFoot _)
      obtain ⟨f,hf,hEnd,hRest⟩ := ih _ hStep
      refine ⟨e.trans f,?_,hEnd,?_⟩
      · change R.2.proj ∘ (f ∘ e) = L.2.proj
        rw [← Function.comp_assoc,hf,he]
      · intro U hAvoid
        obtain ⟨hPair,hTail⟩ := hAvoid
        obtain ⟨χ,hχ,hχIso⟩ := hOpen U (by simpa only [hFoot])
        obtain ⟨ψ,hψ,hψIso⟩ := hRest U hTail
        refine ⟨χ.trans ψ,?_,?_⟩
        · intro z
          change (ψ (χ z)).val = f (e z.val)
          rw [hψ,hχ]
        · simpa only [Diffeomorph.refl_trans] using G3UniverseEmptyAwareCore.trans hχIso hψIso

end Hironaka.HironakaG8FixedGeometricWordReadback
