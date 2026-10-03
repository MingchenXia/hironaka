/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupSNCTransform
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Blowup.SimultaneousNormalCrossings
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.MarkedIdeal.RestrictLe
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Well-formedness of the transform of a marked ideal

Source: Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Definitions 2.1--2.2 and the remark after them
("`𝓘'` is divisible by `𝓘_{σ⁻¹(C)}^d` and `E'` is a normal crossings divisor transverse to `N'`, because `σ` is
admissible").

The transform used is `MarkedIdeal.geoTransform`: strict transforms `closure (π⁻¹(A \ C))` of `N` and of the members
of `E`, followed by `π⁻¹ C`. Its four well-formedness clauses come from:
* `N'` a closed submanifold -- `MarkedIdeal.isClosedSubmanifold_geoTransform_N` (from
  `BlowupStrictIdeal`);
* the transformed ideal coherent -- `MarkedIdeal.isCoherent_geoTransform_ideal`, given
  `𝔞|_N ⊆ 𝓘_C^d|_N` (`hle`; the Hadamard bridge along `N`);
* `E'` SNC and transverse to `N'` -- `BlowupSNCTransform`, given adapted coordinates at the
  points of `C` (`IsAdaptedAt`; automatic for `E = []`, and in general from
  `SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings`).

`isWellFormed_geoTransform_of_isAdmissibleCentre`: the transform of a well-formed marked ideal by
the blowup along ANY admissible centre is well formed, with no further hypothesis.
-/

open Set
open scoped Manifold

universe u

namespace Hironaka.GeoTransformWellFormed

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences NormalCrossings BlowupSNCTransform MarkedIdeals IdealWeightPowers RestrictedIdealWeight

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M']

/-- **The transform of a well-formed marked ideal by an admissible blowup is well formed**, given
`𝔞|_N ⊆ 𝓘_C^d|_N` and adapted coordinates for `C ⊆ N` and `E` at the points of `C`. -/
theorem isWellFormed_geoTransform {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed) {C : Set M}
    {π : M' → M} (hC : 𝔪.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π)
    (hle : RestrictLe 𝔪.N 𝔪.ideal (idealPow (vanishingIdeal (n := n) C) 𝔪.d))
    (hadapt : ∀ x ∈ C, IsAdaptedAt n C 𝔪.N 𝔪.E x) :
    (𝔪.geoTransform C π).IsWellFormed where
  isClosedSubmanifold_N :=
    MarkedIdeal.isClosedSubmanifold_geoTransform_N (𝔪 := 𝔪) (C := C) (π := π)
      h𝔪.isClosedSubmanifold_N hC hπ
  isCoherent :=
    MarkedIdeal.isCoherent_geoTransform_ideal (𝔪 := 𝔪) (C := C) (π := π) h𝔪.isCoherent
      h𝔪.isClosedSubmanifold_N hπ hC.subset_N hle
  isSNCDivisor := isSNCDivisor_geoTransformE hπ h𝔪.isSNCDivisor hadapt
  isTransverse := isTransverse_geoTransformE hπ h𝔪.isClosedSubmanifold_N.1 h𝔪.isSNCDivisor
    h𝔪.isTransverse hadapt

/-- **The transform of a well-formed marked ideal by an admissible blowup is well formed**, given adapted coordinates
at the points of the centre (`𝔞|_N ⊆ 𝓘_C^d|_N` is the Hadamard bridge along `N`, `HadamardBridgeAlong`). -/
theorem isWellFormed_geoTransform_of_adapted {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed)
    {C : Set M} {π : M' → M} (hC : 𝔪.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π)
    (hadapt : ∀ x ∈ C, IsAdaptedAt n C 𝔪.N 𝔪.E x) :
    (𝔪.geoTransform C π).IsWellFormed :=
  isWellFormed_geoTransform h𝔪 hC hπ
    (HadamardBridgeAlong.restrictLe_idealPow_vanishingIdeal_of_subset_cosupport h𝔪.isCoherent
      h𝔪.isClosedSubmanifold_N hC.1 hC.subset_N hC.2.1) hadapt

/-- **The transform of a well-formed marked ideal by the blowup along any admissible centre is
well formed** (Bierstone--Milman 2008, remark after Definitions 2.2), with no further hypothesis:
the adapted coordinates are `SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings`
(the dimension is positive because the centre of a blowup has empty interior). -/
theorem isWellFormed_geoTransform_of_isAdmissibleCentre {𝔪 : MarkedIdeal n M}
    (h𝔪 : 𝔪.IsWellFormed) {C : Set M} {π : M' → M} (hC : 𝔪.IsAdmissibleCentre C)
    (hπ : IsBlowupAlong n C π) : (𝔪.geoTransform C π).IsWellFormed :=
  isWellFormed_geoTransform_of_adapted h𝔪 hC hπ fun _ hx =>
    SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings
      (SimultaneousNormalCrossings.pos_of_isBlowupAlong hπ hx) hC.subset_N h𝔪.isSNCDivisor
      h𝔪.isTransverse hC.2.2 hx

end

end Hironaka.GeoTransformWellFormed
