import Hironaka.Resolution.HironakaG3UniverseShrinkManifold
import Hironaka.Resolution.HironakaG3UniverseLiftManifold
import Hironaka.Resolution.HironakaG3UniverseCarrierGeometry
import Hironaka.Resolution.HironakaG3UniverseDiffeoInvertible
import Hironaka.Resolution.HironakaG3UniverseVanishingIdeal
import Hironaka.Resolution.HironakaSmoothSubmersionContactParameterCoefficientIdeals
set_option autoImplicit false
universe u
namespace Hironaka.G3UniverseBlowupTestLift
open Set Function
open scoped Topology Manifold ContDiff
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  HironakaG3UniverseShrinkManifold G3UniverseSubmersionConjugate G3UniverseVanishingIdeal
  HironakaSmoothSubmersionContactParameterCoefficientIdeals VanishingIdealCoherent
noncomputable section

/-- The actual universe-zero blowup universal property lifts each actual arbitrary-universe test map. -/
theorem conjugate_blowup_unique_lift {n m : ℕ} {X₀ Y₀ : CMfd.{0} n} {X Y : CMfd.{u} n}
    (a : X₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (b : Y₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    {C : Set X₀} {π : Y₀ → X₀} (hπ : IsBlowupAlong n C π)
    (Z : CMfd.{u} m) (g : Z → X)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g)
    (hI : (GermIdeal.pullback (m := m) g (vanishingIdeal (n := n) (a.symm ⁻¹' C))).IsInvertible) :
    ∃! h : Z → Y, ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ h ∧
      (a ∘ π ∘ b.symm) ∘ h = g := by
  let e := shrinkDiffeomorph Z
  let g₀ : shrinkCMfd Z → X₀ := a.symm ∘ g ∘ e.symm
  have hg₀ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g₀ :=
    a.symm.contMDiff.comp (hg.comp e.symm.contMDiff)
  have hVan := pullback_vanishingIdeal_preimage a.symm.contMDiff a.contMDiff
    a.symm_apply_apply a.apply_symm_apply hg C
  rw [hVan] at hI
  have hI₀ := diffeo_pullback_invertible e.symm hI
  have hComp := coherent_parameter_pullback_comp (a.symm.contMDiff.comp hg) e.symm.contMDiff
    (vanishingIdeal (n := n) C) (isCoherent_vanishingIdeal hπ.1)
  rw [← hComp] at hI₀
  obtain ⟨h₀,⟨hh₀,hπ₀⟩,huniq⟩ := hπ.2.2.2.2 m (shrinkCMfd Z) g₀ hg₀ hI₀
  let h : Z → Y := b ∘ h₀ ∘ e
  refine ⟨h,⟨b.contMDiff.comp (hh₀.comp e.contMDiff),?_⟩,?_⟩
  · funext z
    have hz := congrFun hπ₀ (e z)
    simpa [h,g₀,Function.comp_apply] using congrArg a hz
  · intro k hk
    let k₀ : shrinkCMfd Z → Y₀ := b.symm ∘ k ∘ e.symm
    have hk₀ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ k₀ :=
      b.symm.contMDiff.comp (hk.1.comp e.symm.contMDiff)
    have hkπ : π ∘ k₀ = g₀ := by
      funext z
      have hz := congrFun hk.2 (e.symm z)
      have ha := congrArg a.symm hz
      simpa [k₀,g₀,Function.comp_apply] using ha
    have hkEq := huniq k₀ ⟨hk₀,hkπ⟩
    funext z
    have hz := congrFun hkEq (e z)
    simpa [k₀,h,Function.comp_apply] using congrArg b hz
end
end Hironaka.G3UniverseBlowupTestLift

namespace Hironaka.G3UniverseLiftedBlowup
open Set Function
open scoped Topology Manifold ContDiff
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  HironakaG3UniverseLiftManifold HironakaG3UniverseCarrierGeometry G3UniverseBlowupTestLift
  G3UniverseSubmersionConjugate G3UniverseVanishingIdeal
  HironakaSmoothSubmersionContactParameterCoefficientIdeals VanishingIdealCoherent
noncomputable section

/-- The literal universe lift of a universe-zero blowup remains a blowup. -/
theorem lifted_blowup {n : ℕ} {X₀ Y₀ : CMfd.{0} n} {C : Set X₀} {π : Y₀ → X₀}
    (hπ : IsBlowupAlong n C π) :
    let a := liftDiffeomorph.{u} X₀
    let b := liftDiffeomorph.{u} Y₀
    IsBlowupAlong n (a.symm ⁻¹' C) (a ∘ π ∘ b.symm) := by
  let a := liftDiffeomorph.{u} X₀
  let b := liftDiffeomorph.{u} Y₀
  let π' := a ∘ π ∘ b.symm
  have hC : IsClosedSubmanifold n (a.symm ⁻¹' C) := by
    have hh := transported_closedSubmanifold (Homeomorph.ulift.symm) C hπ.1
    exact hh
  have hInt : interior (a.symm ⁻¹' C) = ∅ := by
    have hh := a.symm.toHomeomorph.preimage_interior C
    simp only [Diffeomorph.coe_toHomeomorph, hπ.2.1, Set.preimage_empty] at hh
    exact hh.symm
  have hπ' : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π' :=
    a.contMDiff.comp (hπ.contMDiff.comp b.symm.contMDiff)
  have hInv : (GermIdeal.pullback (m := n) π' (vanishingIdeal (n := n) (a.symm ⁻¹' C))).IsInvertible := by
    have hVan := pullback_vanishingIdeal_preimage a.symm.contMDiff a.contMDiff
      a.symm_apply_apply a.apply_symm_apply hπ' C
    rw [hVan]
    have hEq : a.symm ∘ π' = π ∘ b.symm := by
      funext y
      simp [π',Function.comp_apply]
    rw [hEq]
    have hComp := coherent_parameter_pullback_comp hπ.contMDiff b.symm.contMDiff
      (vanishingIdeal (n := n) C) (isCoherent_vanishingIdeal hπ.1)
    rw [hComp]
    exact diffeo_pullback_invertible b.symm hπ.2.2.2.1
  refine ⟨hC,hInt,hπ',hInv,?_⟩
  intro m Z _ _ _ g hg hI
  exact conjugate_blowup_unique_lift a b hπ (CMfd.of (n := m) Z) g hg hI
end
end Hironaka.G3UniverseLiftedBlowup
