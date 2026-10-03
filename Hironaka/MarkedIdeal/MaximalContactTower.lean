/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.LocalGiraudTransform
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Blowup.BlowupFunctionTransform
import Hironaka.MarkedIdeal.DerivativeIdealTower
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.Blowup.BlowupStrictSubmanifold
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Hypersurfaces of maximal contact along multiple test blow-ups (Giraud)

Source: Włodarczyk 2005, §2.7, Lemma `le:Giraud` (from Lemma `le:Gi`): if `u` is a tangent direction of `(𝔞, μ)` on
`U`, then along every multiple test blow-up the cosupports of the transforms lie in the strict transforms of `V(u)`
over `U`.

Built on `le:Gi` (1), `le:Gi` (2)–(3) on an open set (`LocalGiraudTransform`, and cuts out, the strict transform of
`V(u) ∩ U`), and transform `geoTransformAlong` / `IsGeoTestTower`.

* `geoStrictTransform_inter_preimage`: strict transforms are local over open sets of the base.

Maximal order is not needed (in the source it only serves to provide tangent directions).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MaximalContactTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal IdealWeightPowers BlowupControlledTransform BlowupFunctionTransform BlowupStrictSubmanifold BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal HomogenizedGlueingTower

noncomputable section

/-- **Strict transforms are local over open subsets of the base**: if `A` and `B` agree on the open set `O`, their
strict transforms agree on `π⁻¹ O`. -/
theorem geoStrictTransform_inter_preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {π : Y → X} (hπ : Continuous π) {O : Set X} (hO : IsOpen O) {C A B : Set X} (hAB : A ∩ O = B ∩ O) :
    geoStrictTransform π C A ∩ π ⁻¹' O = geoStrictTransform π C B ∩ π ⁻¹' O := by
  have key : ∀ {A B : Set X}, A ∩ O = B ∩ O →
      geoStrictTransform π C A ∩ π ⁻¹' O ⊆ geoStrictTransform π C B := by
    intro A B hAB y ⟨hy, hyO⟩
    have h1 : y ∈ closure (π ⁻¹' O ∩ π ⁻¹' (A \ C)) :=
      (hO.preimage hπ).inter_closure ⟨hyO, hy⟩
    refine closure_mono ?_ h1
    rintro x ⟨hxO, hxA, hxC⟩
    have : π x ∈ B ∩ O := hAB ▸ ⟨hxA, hxO⟩
    exact ⟨this.1, hxC⟩
  exact Subset.antisymm (fun y hy => ⟨key hAB hy, hy.2⟩) (fun y hy => ⟨key hAB.symm hy, hy.2⟩)

end

end Hironaka.MaximalContactTower
