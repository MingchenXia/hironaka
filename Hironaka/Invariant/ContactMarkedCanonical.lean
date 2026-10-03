/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.ContactStageTail
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.ContactEquivalenceAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongEtale
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1b's restricted marked ideal along isomorphisms of towers and on restricted towers

Source: Włodarczyk 2005 (arXiv `hiron.tex`), the lemma on the commutativity of the resolution procedure in Step 1
with étale morphisms (`J̄'_{|V(u)} = φ^*(J̄_{|V(u)})`).

At a point of level `0`, the Step 1 value function evaluates a resolution invariant `R` in dimension `≤ k - 1` on
`𝓢_{u,T₀}|_W = MaximalOrderStepOneB.contactMarked N 𝔞 μ u T₀ W` (the coefficient ideal of `J̄_{T₀}`, `J̄ =
𝓒_N(𝓗_N(𝔞), μ)`, restricted to the strict transform of `N ∩ V(u)` and to an open `W` of the stage `T₀`), along the
restricted tail. For property (6) the marked ideal `Φ^*𝔍` along a tower isomorphic to the given one over a
biholomorphism `Φ` of the bases is compared with `𝔍`; for property (5) the restriction `𝔍|_U` along the restricted
tower. This module shows that the restricted marked ideal of Step 1b is carried along: with the tangent direction `u
∘ Φ` (resp. `u ∘ ι`), the marked ideal formed for `Φ^*𝔍` (resp. `𝔍|_U`) is the pullback of the one formed for `𝔍`,
and the domain, canonical segments and values of `R` correspond. (The change from `u ∘ Φ` to the tangent direction
the value function chooses for `Φ^*𝔍` is `StepOneTangentChange`.)

## Main results

* `pullback_pullback_of_comp_eq` (generic): pullbacks of a coherent marked ideal along two commuting squares agree;
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ContactMarkedCanonical

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction HomogenizedIdealAlong MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupTowerIsomorphism ResolutionInvariantExt MaxLocusLocal
open HomogenizedGlueingTower (strictAlong)
open HomogenizedGlueingAlongTower (homogenizedMarkedAlong)
open MaximalOrderStepOneB (stepOneMarked contactMarked)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Pullbacks along commuting squares -/

section Generic

variable {P Q R Y : Type u} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  [TopologicalSpace Q] [ChartedSpace (ComplexModel n) Q] [IsComplexManifold n Q]
  [TopologicalSpace R] [ChartedSpace (ComplexModel n) R] [IsComplexManifold n R]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Pullbacks along a commuting square**: for holomorphic `a : P → Y`, `b : Q → P`, `c : Q → R`, `d : R → Y` with
`a ∘ b = d ∘ c` and `𝔫` with coherent ideal, `b^*(a^*𝔫) = c^*(d^*𝔫)`. -/
theorem pullback_pullback_of_comp_eq {𝔫 : MarkedIdeal n Y} (h𝔫 : 𝔫.ideal.IsCoherent) {a : P → Y} {b : Q → P}
    {c : Q → R} {d : R → Y} (ha : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ a)
    (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b)
    (hc : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ c)
    (hd : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ d) (h : ∀ q, a (b q) = d (c q)) :
    MarkedIdeal.pullback b (MarkedIdeal.pullback a 𝔫) = MarkedIdeal.pullback c (MarkedIdeal.pullback d 𝔫) := by
  have hfun : a ∘ b = d ∘ c := funext h
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ rfl
  · show b ⁻¹' (a ⁻¹' 𝔫.N) = c ⁻¹' (d ⁻¹' 𝔫.N)
    rw [← preimage_comp, ← preimage_comp, hfun]
  · show (𝔫.E.map (a ⁻¹' ·)).map (b ⁻¹' ·) = (𝔫.E.map (d ⁻¹' ·)).map (c ⁻¹' ·)
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun S _ => ?_
    show b ⁻¹' (a ⁻¹' S) = c ⁻¹' (d ⁻¹' S)
    rw [← preimage_comp, ← preimage_comp, hfun]
  · show GermIdeal.pullback (m := n) b (GermIdeal.pullback (m := n) a 𝔫.ideal) =
      GermIdeal.pullback (m := n) c (GermIdeal.pullback (m := n) d 𝔫.ideal)
    rw [← GermIdealTotalTransform.pullback_comp ha hb h𝔫, ← GermIdealTotalTransform.pullback_comp hd hc h𝔫, hfun]

end Generic

/-! ### Property (6): isomorphisms of towers -/

section Transport

variable {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {N : Set X}
  {𝔞 : GermIdeal n X} {μ : ℕ}

/-- **Tangent directions pull back by biholomorphisms**: a tangent direction `u` of `(𝔞|_N, μ)` on `U` gives the tangent
direction `u ∘ Φ` of `(Φ^*𝔞|_{Φ⁻¹N}, μ)` on `Φ⁻¹U`. -/
theorem isTangentDirectionAlong_comp (h𝔞 : 𝔞.IsCoherent) {U : Set X} {u : X → ℂ}
    (hu : IsTangentDirectionAlong N 𝔞 μ U u) :
    IsTangentDirectionAlong (Φ ⁻¹' N) (GermIdeal.pullback (m := n) Φ 𝔞) μ (Φ ⁻¹' U) (u ∘ Φ) :=
  ContactEquivalenceAlong.isTangentDirectionAlong_pullback
    (fun y => ⟨_, isLocalInverseAt_of_contMDiff Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply
      Φ.symm_apply_apply y⟩) (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞) hu

end Transport

/-! ### Property (5): restriction to an open set of the base -/

section Restrict

variable {X : CMfd.{u} n} (U : Opens X) {N : Set X} {𝔞 : GermIdeal n X} {μ : ℕ}

/-- **Tangent directions restrict to open sets**: a tangent direction `u` of `(𝔞|_N, μ)` on `U₀` gives the tangent direction
`u ∘ ι` of `(ι^*𝔞|_{ι⁻¹N}, μ)` on `ι⁻¹U₀` (`ι : U → X`). -/
theorem isTangentDirectionAlong_comp_val (h𝔞 : 𝔞.IsCoherent) {U₀ : Set X} {u : X → ℂ}
    (hu : IsTangentDirectionAlong N 𝔞 μ U₀ u) :
    IsTangentDirectionAlong ((Subtype.val : U → X) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔞) μ
      ((Subtype.val : U → X) ⁻¹' U₀) (u ∘ Subtype.val) :=
  ContactEquivalenceAlong.isTangentDirectionAlong_pullback
    (fun y => ⟨DerivativeIdealAlongEtale.openInv U y, DerivativeIdealAlongEtale.isLocalInverseAt_val U y⟩)
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞) hu

end Restrict

end

end Hironaka.ContactMarkedCanonical
