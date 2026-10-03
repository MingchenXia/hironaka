/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Splitting a tower, along restriction to open sets and along isomorphisms of towers

In the maximal-order case and the general step (`hir:maximal-order-step`, `hir:general-step`) the lower-dimensional
invariant at a point is computed along the tail of the split of the segment at a stage depending on the point
(`BlowupTowerSplit.split`). Properties (5) and (6) of `hir:centre-function` for the new invariant compare the split
of a restricted tower `T|_U`, resp. of an isomorphic tower `T'`, with the split of `T`; this module gives the
comparison as isomorphisms of towers (`IsTowerIso`), so that properties (5) and (6) of the inductive invariant apply
to the pieces. Source: Włodarczyk 2005 (arXiv `hiron.tex`), the commutativity of the resolution procedure of Step 1
with étale morphisms (the induced sequence `φ^*(X_i)_{i_l ≤ i ≤ i_{l+1}}` of each part of the resolution).

The restriction `restrict U T` of a tower is not definitionally the concatenation of the restricted pieces (the stages agree
only propositionally), so the comparisons are isomorphisms of towers whose last-stage maps are the identity on points.

## Main results

* `IsTowerIso.congr_last`: an isomorphism of towers may be stated with any pointwise equal last-stage map, resp.
  base biholomorphism;
* `exists_isTowerIso_split_restrict`: **the split of a restricted tower is the restriction of the split** -- the
  head of `split (restrict U T) j` is isomorphic over `id_U` to `restrict U (head T j)`, and its tail, over that
  isomorphism, to `restrict (openPreimage (head T j) U) (tail T j)` with last-stage map the identity on points
* `IsTowerIso.exists_split`: **splits correspond along isomorphisms of towers** -- for `IsTowerIso Φ T' T χ` the heads of the
  splits at `j` are isomorphic over `Φ` and the tails over that isomorphism, with last-stage map `χ`.
-/

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.BlowupTowerSplitIso

open Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerIsomorphism Hironaka.BlowupTowerSplit Hironaka.BlowupRestrictOpen Hironaka.BlowupTowerIsoTail

noncomputable section

variable {n : ℕ}

/-! ### Changing the maps of an isomorphism of towers -/

section Congr

variable {X X' : CMfd.{u} n} {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X} {Y' Y : CMfd.{u} n}
  {T' : BlowupTower X' Y'} {T : BlowupTower X Y} {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}

/-- An isomorphism of towers may be stated with any pointwise equal last-stage map. -/
theorem IsTowerIso.congr_last (h : IsTowerIso Φ T' T χ)
    {χ' : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (hχ : ∀ p, χ' p = χ p) : IsTowerIso Φ T' T χ' := by
  obtain rfl : χ' = χ := Diffeomorph.ext hχ
  exact h

end Congr

/-! ### Restriction of a split tower -/

section Restrict

variable {X : CMfd.{u} n}

/-- The open preimage of `U` in the last stage of `T` is that of the open preimage in the head stage, along the tail. -/
theorem openPreimage_head_tail (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ) :
    openPreimage T U = openPreimage (tail T j) (openPreimage (head T j) U) := by
  rw [openPreimage_append, head_append_tail]

/-- **The split of a restricted tower is the restriction of the split**: the head of `split (restrict U T) j` is
isomorphic over `id_U` to `restrict U (head T j)`, by some `χ₀`, and the tail of `split (restrict U T) j` is isomorphic over
`χ₀` to `restrict (openPreimage (head T j) U) (tail T j)`, with last-stage map the identity on points. -/
theorem exists_isTowerIso_split_restrict (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ),
      ∃ χ₀ : (split (restrict U T) j).1 ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage (head T j) U),
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) (head (restrict U T) j)
          (restrict U (head T j)) χ₀ ∧
        IsTowerIso χ₀ (tail (restrict U T) j) (restrict (openPreimage (head T j) U) (tail T j))
          (opensCongr (openPreimage_head_tail U T j))
  | _, .refl, 0 =>
      ⟨Diffeomorph.refl _ _ _, IsTowerIso.refl,
        IsTowerIso.congr_last IsTowerIso.refl fun _ => rfl⟩
  | _, .step T C π hπ, 0 =>
      ⟨Diffeomorph.refl _ _ _, IsTowerIso.refl_self _,
        IsTowerIso.congr_last IsTowerIso.refl fun _ => rfl⟩
  | _, .refl, _ + 1 =>
      ⟨Diffeomorph.refl _ _ _, IsTowerIso.refl,
        IsTowerIso.congr_last IsTowerIso.refl fun _ => rfl⟩
  | _, .step T C π hπ, j + 1 => by
      obtain ⟨χ₀, h₀, h₁⟩ := exists_isTowerIso_split_restrict U T j
      refine ⟨χ₀, h₀, ?_⟩
      exact IsTowerIso.step h₁ _ _ _ (fun _ => rfl) rfl

end Restrict

/-! ### Splits along isomorphisms of towers -/

section Iso

variable {X X' : CMfd.{u} n}

/-- **Splits correspond along isomorphisms of towers**: if `χ : T' ≅ T` over `Φ`, then for every `j` the heads of the
splits at `j` are isomorphic over `Φ`, by some `χ₀`, and the tails are isomorphic over `χ₀` with last-stage map `χ`. -/
theorem IsTowerIso.exists_split {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X} {Y' Y : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y} {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (h : IsTowerIso Φ T' T χ) (j : ℕ) :
    ∃ χ₀ : (split T' j).1 ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (split T j).1,
      IsTowerIso Φ (head T' j) (head T j) χ₀ ∧ IsTowerIso χ₀ (tail T' j) (tail T j) χ := by
  induction h generalizing j with
  | refl =>
    cases j with
    | zero => exact ⟨Φ, IsTowerIso.refl, IsTowerIso.refl⟩
    | succ j => exact ⟨Φ, IsTowerIso.refl, IsTowerIso.refl⟩
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    cases j with
    | zero => exact ⟨χ₁, IsTowerIso.step h hπ' hπ χ₁ hcomm hC, IsTowerIso.refl⟩
    | succ j =>
      obtain ⟨χ₀, h₀, h₁⟩ := ih j
      exact ⟨χ₀, h₀, IsTowerIso.step h₁ hπ' hπ χ₁ hcomm hC⟩

end Iso

end

end Hironaka.BlowupTowerSplitIso
