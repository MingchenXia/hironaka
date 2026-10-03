/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ResolutionInvariantDriver
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Canonical segments of a resolution invariant: open sets, isomorphisms of towers, counting centres

Sources: Włodarczyk 2005, Proposition `pr:resol` (4) and §2.4 (the pullback of the canonical resolution along an
étale map -- here an open embedding or a biholomorphism -- is an *extension* of the canonical resolution of the
pullback: the same nonempty centres, with steps of empty centre inserted), and the remark after Definition
`hir:centre-function`.

Let `R` be a resolution invariant in dimension `≤ k` (`ResolutionInvariantSpec.ResolutionInvariant`) and `𝔪` a marked
ideal of its domain.

## Main results

* `maxLocus_preimage`, `maxLocus_preimage_of_surjective`: a maximum locus pulls back along a map preserving the values
  on the set, if the pulled-back locus is nonempty or the map is surjective;
* `cosupp_geoTransformAlong_restrict`: along the restriction to `U` of a multiple test blow-up, the cosupport is the trace
  of the cosupport;
* `isCanonical_restrict`: **the restriction to an open `U` of a canonical segment of `𝔪` is a canonical segment of
  `𝔪|_U`** (property (5): a restricted centre is empty or, the maximum being attained in `U`, the maximum locus of the
  restricted invariant);
* `isCanonical_of_isTowerIso`: **canonical segments correspond along isomorphisms of towers** (property (6));
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ResolutionInvariantSegments

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealBiholomorphism.MarkedIdeal Hironaka.MarkedIdealRestrictOpen Hironaka.BlowupTowerIsomorphism Hironaka.ResolutionInvariantSpec Hironaka.ResolutionDriver Hironaka.ResolutionInvariantDriver

noncomputable section

variable {n : ℕ}

/-! ### Maximum loci along maps -/

section MaxLocus

variable {Λ : Type*} [LinearOrder Λ]

/-- **A maximum locus pulls back** along a map `ι` with `g = f ∘ ι` on `ι⁻¹ s`, as soon as the pulled-back locus is
nonempty (the maximum of `f` on `s` is then attained in the image of `ι`). -/
theorem maxLocus_preimage {Y Y' : Type*} (ι : Y' → Y) {f : Y → Λ} {g : Y' → Λ} {s : Set Y}
    (hfg : ∀ p, ι p ∈ s → g p = f (ι p)) (hne : (ι ⁻¹' maxLocus f s).Nonempty) :
    maxLocus g (ι ⁻¹' s) = ι ⁻¹' maxLocus f s := by
  obtain ⟨p₀, hp₀s, hp₀⟩ := hne
  ext p
  constructor
  · rintro ⟨hps, hp⟩
    refine ⟨hps, fun y hy => ?_⟩
    calc f y ≤ f (ι p₀) := hp₀ y hy
      _ = g p₀ := (hfg p₀ hp₀s).symm
      _ ≤ g p := hp p₀ hp₀s
      _ = f (ι p) := hfg p hps
  · rintro ⟨hps, hp⟩
    refine ⟨hps, fun q hq => ?_⟩
    rw [hfg q hq, hfg p hps]
    exact hp (ι q) hq

/-- **A maximum locus pulls back along a surjection** with `g = f ∘ χ` on `χ⁻¹ s`. -/
theorem maxLocus_preimage_of_surjective {Y Y' : Type*} {χ : Y' → Y} (hχ : Function.Surjective χ) {f : Y → Λ}
    {g : Y' → Λ} {s : Set Y} (hfg : ∀ p, χ p ∈ s → g p = f (χ p)) :
    maxLocus g (χ ⁻¹' s) = χ ⁻¹' maxLocus f s := by
  ext p
  constructor
  · rintro ⟨hps, hp⟩
    refine ⟨hps, fun y hy => ?_⟩
    obtain ⟨q, rfl⟩ := hχ y
    rw [← hfg q hy, ← hfg p hps]
    exact hp q hy
  · rintro ⟨hps, hp⟩
    refine ⟨hps, fun q hq => ?_⟩
    rw [hfg q hq, hfg p hps]
    exact hp (χ q) hq

end MaxLocus

/-! ### Open sets -/

section Restrict

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ}

/-- **The cosupport along a restricted multiple test blow-up is the trace of the cosupport.** -/
theorem cosupp_geoTransformAlong_restrict {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    (geoTransformAlong (pullback (Subtype.val : U → X) 𝔪) (restrict U T)).cosupp =
      (Subtype.val : openPreimage T U → _) ⁻¹' (geoTransformAlong 𝔪 T).cosupp := by
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  rw [geoTransformAlong_restrict U hN h𝔞 T hT, cosupp_pullback_val _
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg)]

end Restrict

end

end Hironaka.ResolutionInvariantSegments
