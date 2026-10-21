/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalGlobalPrincipalization
import Hironaka.Analytic.SNCDivisorLocalGenerator

/-! Actual local SNC geometry of the same original global principalization divisor.
The entire real terminal boundaries and literal restricted global ideal are
retained through the genuine local range biholomorphisms. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalGlobalSNCPrincipalization
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalTerminalLocalBiholomorphism HironakaOriginalGlobalPrincipalization
open ResolutionInvariantSpec (IsInvDomain)
attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

variable {n : ℕ} {X : CMfd.{u} n}

/-- The full actual terminal boundary, with every position preserved, on the
genuine original saturated global range. -/
def originalTerminalRangeBoundary (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    List (Set (originalTerminalLocalRangeOpen M hM i)) :=
  (geoTransformAlong
    (MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : (actualLocalTerminalAtlas M hM).openSet i → X) M)
    ((actualLocalTerminalAtlas M hM).tower i)).E.map
      ((originalTerminalLocalBiholomorphism M hM i).symm ⁻¹' ·)

/-- Genuine transformed wellformedness and biholomorphic coordinate transport
prove actual SNC on the same global range, before using any divisor support. -/
theorem originalTerminalRangeBoundary_isSNCDivisor
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    IsSNCDivisor n (originalTerminalRangeBoundary M hM i) := by
  have hdom := InvDomainTowerAlong.isInvDomain_pullback_val
    ((actualLocalTerminalAtlas M hM).openSet i) hM
  have hs := (InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom
    ((actualLocalTerminalAtlas M hM).tower i) ((actualLocalTerminalAtlas M hM).terminal i).1).isWellFormed.isSNCDivisor
  exact (MarkedIdealTowerTransport.isSNCDivisor_map_preimage_iff
    (originalTerminalLocalBiholomorphism M hM i).symm).mpr hs

/-- The effective divisor of the literal true global ideal restricted to its
actual original saturated range. -/
def originalTerminalRangePrincipalizationDivisor
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1) (i : X) :
    EffectiveDivisor n (originalTerminalLocalRangeOpen M hM i) where
  ideal := GermIdeal.pullback (m := n)
    (Subtype.val : originalTerminalLocalRangeOpen M hM i → originalTerminalManifold M hM)
    (originalTerminalPrincipalizationDivisor M hM hN hd).ideal
  isInvertible := originalTerminalRange_pullback_isInvertible M hM hN hd i

theorem originalTerminalRangePrincipalizationDivisor_ideal
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1) (i : X) :
    (originalTerminalRangePrincipalizationDivisor M hM hN hd i).ideal =
      GermIdeal.pullback (m := n)
        (Subtype.val : originalTerminalLocalRangeOpen M hM i → originalTerminalManifold M hM)
        (originalTerminalPrincipalizationDivisor M hM hN hd).ideal := rfl

/-- The actual restricted global divisor support is exactly the whole genuine
ordered terminal SNC family, with original empty initial boundary. -/
theorem originalTerminalRangePrincipalizationDivisor_support
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1)
    (hE : M.E = []) (i : X) :
    (originalTerminalRangePrincipalizationDivisor M hM hN hd i).support =
      ⋃ H ∈ originalTerminalRangeBoundary M hM i, H := by
  let A := actualLocalTerminalAtlas M hM
  let M' := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : A.openSet i → X) M
  have hE' : M'.E = [] := by
    change M.E.map ((Subtype.val : A.openSet i → X) ⁻¹' ·) = []
    rw [hE, List.map_nil]
  have hs := HironakaPrincipalization.support_exceptionalDivisor_eq_biUnion M' hE' (A.tower i)
  change (GermIdeal.pullback (m := n)
    (Subtype.val : originalTerminalLocalRangeOpen M hM i → originalTerminalManifold M hM)
    (GermIdeal.pullback (m := n)
      (originalTerminalGluedProjection M hM : originalTerminalManifold M hM → X) M.ideal)).zeroLocus = _
  erw [originalTerminalRange_pullback_ideal M hM hN hd i,
    BlowupExceptionalDivisor.zeroLocus_pullback
      (originalTerminalLocalBiholomorphism M hM i).symm.contMDiff
      (BlowupExceptionalDivisor.isCoherent_ideal (exceptionalDivisor (A.tower i)))]
  change (originalTerminalLocalBiholomorphism M hM i).symm ⁻¹'
    (exceptionalDivisor (A.tower i)).support =
      ⋃ H ∈ (geoTransformAlong M' (A.tower i)).E.map
        ((originalTerminalLocalBiholomorphism M hM i).symm ⁻¹' ·), H
  rw [hs]
  ext q
  simp only [mem_preimage, mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨H, hH, hq⟩
    exact ⟨(originalTerminalLocalBiholomorphism M hM i).symm ⁻¹' H, ⟨H, hH, rfl⟩, hq⟩
  · rintro ⟨_, ⟨H, hH, rfl⟩, hq⟩
    exact ⟨H, hH, hq⟩

/-- Every actual global range point has an adapted unit-monomial generator of
the literal restricted global principalization ideal. All geometric data are
internally produced from original marked input and its actual terminal charts. -/
theorem exists_originalTerminalRange_unit_monomial_generator
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1)
    (hE : M.E = []) (i : X) (x : originalTerminalLocalRangeOpen M hM i) :
    let R := originalTerminalLocalRangeOpen M hM i
    let E := originalTerminalRangeBoundary M hM i
    ∃ U : Set R, IsOpen U ∧ x ∈ U ∧ ∃ g : R → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g U ∧
      (∀ W : Set R, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0) ∧
      (∀ y ∈ U, ∀ f : R → ℂ,
        (GermIdeal.pullback (m := n) (Subtype.val : R → originalTerminalManifold M hM)
          (originalTerminalPrincipalizationDivisor M hM hN hd).ideal).mem y f ↔
            IsInSpanAt (n := n) (· = g) y f) ∧
      ∃ (S : Fin E.length → Finset (Fin n))
        (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x)),
        Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
        Φ.toFun ((complexChartAt (n := n) x).val x) = 0 ∧
        (∀ j, x ∈ E.get j → (S j).card = 1) ∧ Set.InjOn S {j | x ∈ E.get j} ∧
        (∀ j, x ∈ E.get j → ∀ {y : R}, y ∈ (complexChartAt (n := n) x).val.source →
          (complexChartAt (n := n) x).val y ∈ Φ.source →
          (y ∈ E.get j ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S j))) ∧
        ∃ (a : Fin n → ℕ) (H : ComplexModel n → ℂ),
          (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z) ∧ H 0 ≠ 0 ∧
          (fun z => g ((complexChartAt (n := n) x).val.symm (Φ.invFun z))) =ᶠ[𝓝 0]
            fun z => H z * ∏ j : Fin n, z j ^ a j := by
  dsimp only
  exact SNCDivisorLocalGenerator.exists_adapted_unit_monomial_generator
    (originalTerminalRangePrincipalizationDivisor M hM hN hd i)
    (originalTerminalRangeBoundary M hM i) (originalTerminalRangeBoundary_isSNCDivisor M hM i)
    (originalTerminalRangePrincipalizationDivisor_support M hM hN hd hE i) x

end
end Hironaka.HironakaOriginalGlobalSNCPrincipalization
