/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.ContactStageInvDomain
import Hironaka.Support.ContactIndependenceTransportExact

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ContactStageInvDomain

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdealAlong
  TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower MarkedIdealEquivalence
  MarkedIdealEquivalence.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen MemberInterTowerAlong
  ContactEquivalenceAlong MaximalContactAlongTower ContactEquivalenceStage DivisorExponentAlong CodimOneSupportAlong
  NormalCrossings
open HomogenizedGlueingTower (strictAlong N_geoTransformAlong)
open ResolutionInvariantSpec (DimLE IsInvDomain)

noncomputable section

variable {n : ℕ}

section Glueing

open HomogenizedGlueingAlongTower HomogenizedGlueingLiftAlong GlueingTrivialAction BlowupTowerIsomorphism
  BlowupTowerIsoTail
open ContactIndependenceAlong (one_le_coeffMarkedAlong_d)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ}

/-- **Glueing data acting trivially, inside the sets of the two tangent directions** (`exists_glueingDataAlong_trivial` with
its open set `W` shrunk to `W ∩ U ∩ U'`). -/
theorem exists_glueingDataAlong_trivial_subset (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    {x : M} (hx : x ∈ cosupport n N 𝔞 μ) {U U' : Set M} (hu : IsTangentDirectionAlong N 𝔞 μ U u) (hxU : x ∈ U)
    (hv : IsTangentDirectionAlong N 𝔞 μ U' v) (hxU' : x ∈ U') :
    ∃ G : GlueingDataAlong N 𝔞 μ u v, x ∈ G.W ∧ G.W ⊆ U ∩ U' ∧ ∀ y ∈ G.W, y ∈ zeroSet (glueIdealAlong N 𝔞 μ) →
      TrivialAt G.φ (glueIdealAlong N 𝔞 μ) y ∧ TrivialAt G.ψ (glueIdealAlong N 𝔞 μ) y := by
  obtain ⟨G, hxW, htriv⟩ := exists_glueingDataAlong_trivial h𝔞 hN hμ hx hu hxU hv hxU'
  refine ⟨⟨G.φ, G.ψ, G.W ∩ (U ∩ U'), ⟨G.pair.isOpen.inter (hu.isOpen.inter hv.isOpen),
      fun p hp => G.pair.mdifferentiableAt_left p hp.1, fun p hp => G.pair.mdifferentiableAt_right p hp.1,
      fun p hp => G.pair.left_inv p hp.1, fun p hp => G.pair.right_inv p hp.1⟩,
    fun y hy => G.pullback_iff y hy.1, fun p hp => G.comp_eq p hp.1, fun y hy => G.apply_eq_self y hy.1,
    fun p hp => G.mem_N_iff p hp.1⟩, ⟨hxW, hxU, hxU'⟩, inter_subset_right, fun y hy hz => htriv y hy.1 hz⟩

/-- **`BlowupTowerIsoTail.contact_independence_along_tail` with the glueing neighbourhoods inside the sets of the two
tangent directions**: the domain `U'` and the codomain `U` of the glueing biholomorphism lie in `U₁ ∩ U₂`, so that `u` and
`v` are tangent directions on `U` and `U'` (`isTangentDirectionAlong_mono`) and the stage results
(`ContactEquivalenceStage.isGeoTestTower_tail_coeffHom`, `isInvDomain_stage_coeffHom`) apply with the open set `U`. -/
theorem contact_independence_along_tail_subset (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) {x : M}
    (hx : x ∈ cosupport n N 𝔞 μ) {U₁ U₂ : Set M} (hu : IsTangentDirectionAlong N 𝔞 μ U₁ u) (hxU₁ : x ∈ U₁)
    (hv : IsTangentDirectionAlong N 𝔞 μ U₂ v) (hxU₂ : x ∈ U₂) :
    ∃ G : GlueingDataAlong N 𝔞 μ u v, x ∈ G.dom ∧ x ∈ G.cod ∧ (G.dom : Set M) ⊆ U₁ ∩ U₂ ∧
      (G.cod : Set M) ⊆ U₁ ∩ U₂ ∧
      ∀ {Y Z : CMfd.{u} n} (T₀ : BlowupTower (CMfd.of (n := n) M) Y) (T₁ : BlowupTower Y Z),
        IsGeoTestTower (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) (T₀.append T₁) →
        ∃ (Φ₀ : CMfd.of (n := n) (openPreimage T₀ G.dom) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
              CMfd.of (n := n) (openPreimage T₀ G.cod))
          (χ : CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ G.dom))
            ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
              CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ G.cod))),
          IsGlueingLiftAlong G T₀ Φ₀ ∧
          IsTowerIso Φ₀ (restrict (openPreimage T₀ G.dom) T₁) (restrict (openPreimage T₀ G.cod) T₁) χ ∧
          MarkedIdeal.pullback Φ₀ (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ G.cod → Y)
              (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀))
                (strictAlong T₀ (N ∩ {x | u x = 0})))) =
            MarkedIdeal.pullback (Subtype.val : openPreimage T₀ G.dom → Y)
              (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀))
                (strictAlong T₀ (N ∩ {x | v x = 0}))) ∧
          ∀ p : openPreimage T₁ (openPreimage T₀ G.dom),
            (p : Z) ∈ (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) (T₀.append T₁)).cosupp →
              (χ p : Z) = p := by
  obtain ⟨G, hxW, hWsub, htriv⟩ := exists_glueingDataAlong_trivial_subset h𝔞 hN hμ hx hu hxU₁ hv hxU₂
  obtain ⟨hxd, hxc⟩ := G.mem_dom_and_mem_cod hxW hx
  refine ⟨G, hxd, hxc, fun p hp => hWsub hp.1, fun q hq => hWsub hq.1, fun T₀ T₁ hT => ?_⟩
  obtain ⟨Φ₀, χ, hL₀, -, hχ, -, hS₀, -, -, hfix⟩ := exists_isTowerIso_tail_coeffHom G h𝔞 hN hμ htriv T₀ T₁ hT
  exact ⟨Φ₀, χ, hL₀, hχ, hS₀, hfix⟩

end Glueing
end
end Hironaka.ContactStageInvDomain
