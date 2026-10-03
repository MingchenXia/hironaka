/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.GeoTransformWellFormed
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Local biholomorphisms: biholomorphisms between open subsets, and towers along them

Sources: Włodarczyk 2005 §2.4 (Proposition `pr:funct`, étale neighbourhoods) and the Glueing Lemma `le:homo` (4)
(the multiple test blow-ups induced by two étale neighbourhoods `φ_u, φ_v: X̄ → X`); in the analytic setting the
étale neighbourhoods are an open inclusion and a biholomorphism between open sets.

* `contMDiffAt_of_eventually_mdifferentiableAt'`: a map between complex manifolds that is holomorphic near a point is
  `C^∞` there (the normed-space case is `HolomorphicIdealSheaves.contMDiffAt_of_eventually_mdifferentiableAt`);
* `isWellFormed_geoTransformAlong`: every stage of a multiple test blow-up of a well-formed marked ideal is well
  formed (one-step `GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre`, by induction);
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MarkedIdealOpenBiholomorphism

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealTowerTransport Hironaka.MarkedIdealRestrictOpen Hironaka.BlowupTowerTransforms Hironaka.BlowupRestrictOpen

noncomputable section

/-! ### Biholomorphisms between open subsets -/

section Open

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A map that is holomorphic near a point is `C^∞` there** (target a complex manifold). -/
theorem contMDiffAt_of_eventually_mdifferentiableAt' {m : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y] {f : Y → M} {y : Y}
    (hf : ∀ᶠ y' in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f y') :
    ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y := by
  have hc : ContinuousAt f y := hf.self_of_nhds.continuousAt
  rw [contMDiffAt_iff_target]
  refine ⟨hc, contMDiffAt_of_eventually_mdifferentiableAt ?_⟩
  filter_upwards [hf, hc.preimage_mem_nhds
    ((chartAt (ComplexModel n) (f y)).open_source.mem_nhds (mem_chart_source _ _))] with y' hy' hy's
  exact (mdifferentiableAt_extChartAt hy's).comp y' hy'

end Open

/-! ### Well-formed stages -/

section WellFormed

variable {n : ℕ} {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X}

/-- **Every stage of a multiple test blow-up of a well-formed marked ideal is well formed.** -/
theorem isWellFormed_geoTransformAlong (h : 𝔪.IsWellFormed) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T → (geoTransformAlong 𝔪 T).IsWellFormed
  | _, .refl, _ => h
  | _, .step T _ _ hπ, hT =>
      GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
        (isWellFormed_geoTransformAlong h T hT.1) hT.2 hπ

end WellFormed

end

end Hironaka.MarkedIdealOpenBiholomorphism
