/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalIdeal
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.InvertibleIdealQuotient

/-!
# The entire actual centre ideal sheaf under a zero section

Both inclusions hold at EVERY actual base point for EVERY subset. The
reverse inclusion uses the literal ambient function g composed with the real
projection, not an origin-germ approximation or a caller extension certificate.
The geometric smoothness of a blowup centre and the induced blowup map remain
separate producers. Blueprint: hironaka-actual-zero-section-centre-sheaf-extension.tex.
Source-only draft; no kernel acceptance claim.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualZeroSectionCentreSheaf

noncomputable section

open Hironaka.HolomorphicIdealSheaves
  HironakaRelativeNormalIdeal InvertibleIdealQuotient

section Retraction

variable {m n : ℕ} {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel m) X] [IsComplexManifold m X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- A true holomorphic retraction supplies BOTH entire vanishing ideal sheaf
directions, at every point and with no regularity hypothesis on the subset. -/
theorem pullback_vanishingIdeal_image_of_holomorphic_retraction
    (i : X → Y) (p : Y → X)
    (hi : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ i)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ p)
    (hpi : Function.LeftInverse p i) (C : Set X) :
    GermIdeal.pullback (m := m) i (vanishingIdeal (n := n) (i '' C)) =
      vanishingIdeal (n := m) C := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ?_)
  constructor
  · intro hg
    obtain ⟨hgh, k, s, a, hs, _ha, hsum⟩ := hg
    refine ⟨hgh, ?_⟩
    have hzero : ∀ j : Fin k, ∀ᶠ z in 𝓝 x, z ∈ C → s j z = 0 := by
      intro j
      obtain ⟨b, hb, hsb⟩ := hs j
      filter_upwards [hi.continuous.continuousAt.eventually hb.2] with z hz hzC
      rw [hsb]
      exact hz ⟨z, hzC, rfl⟩
    filter_upwards [hsum, eventually_all.mpr hzero] with z hzSum hzZero hzC
    rw [hzSum]
    exact Finset.sum_eq_zero fun j _ => by rw [hzZero j hzC, mul_zero]
  · intro hg
    have hpg : HolomorphicAt m g (p (i x)) := by
      simpa only [hpi x] using hg.1
    have hpTendsto : Tendsto p (𝓝 (i x)) (𝓝 x) := by
      simpa only [hpi x] using hp.continuous.tendsto (i x)
    have hLift : (vanishingIdeal (n := n) (i '' C)).mem (i x) (g ∘ p) := by
      refine ⟨hpg.comp_contMDiff (Eventually.of_forall fun y => hp y), ?_⟩
      filter_upwards [hpTendsto.eventually hg.2] with y hy
      rintro ⟨z, hzC, rfl⟩
      exact hy (by simpa only [hpi z] using hzC)
    have hcomp : g = (g ∘ p) ∘ i := by
      funext z
      simp only [Function.comp_apply, hpi z]
    exact isInSpanAt_self
      (S := fun s => ∃ b, (vanishingIdeal (n := n) (i '' C)).mem (i x) b ∧ s = b ∘ i)
      ⟨g ∘ p, hLift, hcomp⟩ hg.1

end Retraction

/-- The SAME literal zero-section centre has exactly the original inverse image. -/
theorem actual_zeroSection_centre_preimage (d t : ℕ) (C : Set (ComplexModel d)) :
    (tangentInclusion d t) ⁻¹' ((tangentInclusion d t) '' C) = C := by
  ext x
  constructor
  · rintro ⟨z, hzC, he⟩
    have hzx : z = x := by
      have h := congrArg (tangentProjection d t) he
      simpa only [tangentProjection_tangentInclusion] using h
    exact hzx ▸ hzC
  · intro hxC
    exact ⟨x, hxC, rfl⟩

/-- ONLY the actual coordinate dimensions and arbitrary subset supply the
whole SHEAF dictionary internally; this quantifies over all points, not just 0. -/
theorem actual_zeroSection_centre_sheaf (d t : ℕ) (C : Set (ComplexModel d)) :
    GermIdeal.pullback (m := d) (tangentInclusion d t)
        (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C)) =
      vanishingIdeal (n := d) C := by
  exact pullback_vanishingIdeal_image_of_holomorphic_retraction
    (tangentInclusion d t) (tangentProjection d t)
    (tangentInclusion d t).contDiff.contMDiff
    (tangentProjection d t).contDiff.contMDiff
    (fun z => tangentProjection_tangentInclusion d t z) C

end
end Hironaka.HironakaActualZeroSectionCentreSheaf
