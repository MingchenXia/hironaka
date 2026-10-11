/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupUniqueness
import Hironaka.Blowup.BlowupTowers
import Mathlib.Geometry.Manifold.Diffeomorph
import Hironaka.Blowup.BlowupBijectiveComparison

set_option autoImplicit false

/-!
# Actual comparison cocycles for a family of blowups of a common centre

Blueprint `hironaka-blowup-cocycle-extension.tex`. The maps and their
cocycle identities are produced by actual analytic blowup uniqueness.
This supplies the comparison-cocycle component of descent once genuine
local centres have been aligned; it does not assume or produce that alignment.
-/

open Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.HironakaBlowupComparisonCocycle

open Hironaka.BlowupSequences BlowupTowers

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n} {I : Type*} (Y : I → CMfd.{u} n)
  {C : Set X} (π : ∀ i, Y i → X)

private theorem comparison_eq_of_over (i j : I)
    (hπ : ∀ i, IsBlowupAlong n C (π i)) {f g : Y i → Y j}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hcompf : π j ∘ f = π i) (hcompg : π j ∘ g = π i) : f = g := by
  obtain ⟨e, -, huniq⟩ := BlowupUniqueness.existsUnique_comparison (hπ i) (hπ j)
  exact (huniq f ⟨hf, hcompf⟩).trans (huniq g ⟨hg, hcompg⟩).symm

/-- Actual blowups of the same smooth centre produce simultaneous pairwise
bijective holomorphic comparisons with actual identity and triple cocycle. -/
theorem exists_comparison_cocycle (hπ : ∀ i, IsBlowupAlong n C (π i)) :
    ∃ f : ∀ i j, Y i → Y j,
      (∀ i j, Function.Bijective (f i j) ∧
        ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (f i j) ∧
        π j ∘ f i j = π i) ∧
      (∀ i, f i i = id) ∧
      ∀ i j k, f j k ∘ f i j = f i k := by
  choose f hf hhol hcomp using fun i j =>
    BlowupUniqueness.bijective_comparison (hπ i) (hπ j)
  refine ⟨f, fun i j => ⟨hf i j, hhol i j, hcomp i j⟩, ?_, ?_⟩
  · intro i
    exact comparison_eq_of_over Y π i i hπ (hhol i i) contMDiff_id (hcomp i i) rfl
  · intro i j k
    apply comparison_eq_of_over Y π i k hπ ((hhol j k).comp (hhol i j)) (hhol i k)
    · calc
        π k ∘ (f j k ∘ f i j) = (π k ∘ f j k) ∘ f i j := rfl
        _ = π i := by rw [hcomp j k, hcomp i j]
    · exact hcomp i k

/-- The genuine comparisons organize into actual biholomorphisms whose
inverses are the reverse comparisons, with the produced cocycle unchanged. -/
theorem exists_biholomorphism_cocycle (hπ : ∀ i, IsBlowupAlong n C (π i)) :
    ∃ Φ : ∀ i j, Y i ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y j,
      (∀ i j, π j ∘ Φ i j = π i) ∧
      (∀ i, (Φ i i : Y i → Y i) = id) ∧
      (∀ i j k, (Φ j k : Y j → Y k) ∘ (Φ i j : Y i → Y j) = Φ i k) ∧
      ∀ i j, (Φ i j).symm.toEquiv.toFun = (Φ j i).toEquiv.toFun := by
  obtain ⟨f, hf, hself, hcocycle⟩ := exists_comparison_cocycle Y π hπ
  let Φ : ∀ i j, Y i ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y j :=
    fun i j => ⟨⟨f i j, f j i,
      congrFun ((hcocycle i j i).trans (hself i)),
      congrFun ((hcocycle j i j).trans (hself j))⟩, (hf i j).2.1, (hf j i).2.1⟩
  exact ⟨Φ, fun i j => (hf i j).2.2, hself, hcocycle, fun _ _ => rfl⟩

end

end Hironaka.HironakaBlowupComparisonCocycle
