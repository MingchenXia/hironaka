/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionGlobalBlowupSubmersion
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionBlowupChoiceGeometry
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupConstruction HironakaSmoothSubmersionBlowupLift
  HironakaSmoothSubmersionNormalCrossings HironakaSmoothSubmersionGlobalBlowupSubmersion
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaNormalCrossingsSeparationChoiceComparison
noncomputable section
section Comparison
variable {n r : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} (n+r)}
  {f : Y → X} {C : Set X} {π : D → X} {π' : D' → Y}

theorem exists_actual_comparison_conjugate
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong (n+r) (f ⁻¹' C) π') :
    let _ : Fact (IsClosedSubmanifold n C) := ⟨hπ.1⟩
    let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) := ⟨(actual_source_centre hf hπ).1⟩
    let h₀ := isBlowupAlong_blowupProj (n := n) (C := C) hπ.2.1
    let h₀' := isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C) (actual_source_centre hf hπ).2
    ∃ a : D ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ BlowupSpace n C,
      ∃ b : D' ≃ₘ⟮𝓘(ℂ, ComplexModel (n+r)),𝓘(ℂ, ComplexModel (n+r))⟯ BlowupSpace (n+r) (f ⁻¹' C),
        (∀ z, blowupProj n C (a z) = π z) ∧
        (∀ z, blowupProj (n+r) (f ⁻¹' C) (b z) = π' z) ∧
        actualLift hf hπ hπ' = a.symm ∘
          actualLift (D := CMfd.of (BlowupSpace n C))
            (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf h₀ h₀' ∘ b := by
  let _ : Fact (IsClosedSubmanifold n C) := ⟨hπ.1⟩
  let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) := ⟨(actual_source_centre hf hπ).1⟩
  dsimp only
  let h₀ := isBlowupAlong_blowupProj (n := n) (C := C) hπ.2.1
  let h₀' := isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C) (actual_source_centre hf hπ).2
  obtain ⟨a,ha,_⟩ := exists_unique_lift (B' := D) (B := CMfd.of (BlowupSpace n C))
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞) hπ h₀ (by rfl)
  obtain ⟨b,hb,_⟩ := exists_unique_lift (B' := D') (B := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C)))
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel (n+r)) Y ∞) hπ' h₀' (by rfl)
  let G₀ := actualLift (D := CMfd.of (BlowupSpace n C))
    (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf h₀ h₀'
  have hapi (z : BlowupSpace n C) : π (a.symm z) = blowupProj n C z := by
    simpa using (ha (a.symm z)).symm
  have hs : π ∘ (a.symm ∘ G₀ ∘ b) = f ∘ π' := by
    funext z
    change π (a.symm (G₀ (b z))) = f (π' z)
    rw [hapi]
    have hh := congrFun (actualLift_proj_comm (D := CMfd.of (BlowupSpace n C))
      (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf h₀ h₀') (b z)
    change blowupProj n C (G₀ (b z)) = f (blowupProj (n+r) (f ⁻¹' C) (b z)) at hh
    rw [hh]
    exact congrArg f (hb z)
  refine ⟨a,b,ha,hb,?_⟩
  exact (actualLift_unique hf hπ hπ' (a.symm ∘ G₀ ∘ b)
    (a.symm.contMDiff.comp ((actualLift_contMDiff hf h₀ h₀').comp b.contMDiff)) hs).symm

theorem actualLift_isSubmersionOfComplement
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong (n+r) (f ⁻¹' C) π') :
    Manifold.IsSubmersionOfComplement (ComplexModel r)
      𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ (actualLift hf hπ hπ') := by
  let _ : Fact (IsClosedSubmanifold n C) := ⟨hπ.1⟩
  let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) := ⟨(actual_source_centre hf hπ).1⟩
  obtain ⟨a,b,_,_,he⟩ := exists_actual_comparison_conjugate hf hπ hπ'
  have hG₀ := canonical_actualLift_isSubmersion hf C hπ.1 hπ.2.1
  have hG := isSubmersion_conjugate (A := CMfd.of (BlowupSpace n C)) (A' := D)
    (B := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) (B' := D') a b hG₀
  rw [he]
  intro z
  let h := hG.isSubmersionAt z
  have hh := h.isSubmersionAtOfComplement_complement.trans_F (complementCoordinates h)
  change Manifold.IsSubmersionAtOfComplement (ComplexModel (n+r-n))
    𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ _ z at hh
  exact hh.trans_F (ContinuousLinearEquiv.ofFinrankEq (show Module.finrank ℂ (ComplexModel (n+r-n)) =
    Module.finrank ℂ (ComplexModel r) by simp only [ComplexModel,finrank_euclideanSpace_fin]; omega))

end Comparison

section AnyDimension
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {C : Set X} {π : D → X} {π' : D' → Y}

theorem actualLift_isSubmersion
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π') :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (actualLift hf hπ hπ') := by
  classical
  by_cases hd : Nonempty D'
  · obtain ⟨p⟩ := hd
    have hnm := HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt (hf.isSubmersionAt (π' p))
    obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hnm
    subst m
    exact (actualLift_isSubmersionOfComplement hf hπ hπ').isSubmersion
  · have : IsEmpty D' := not_nonempty_iff.mp hd
    apply Manifold.IsSubmersionOfComplement.isSubmersion (F := ComplexModel 0)
    intro z
    exact (IsEmpty.false z).elim

theorem exists_original_smooth_blowup_lift
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) :
    ∃ (Z : CMfd.{u} m) (ρ : Z → Y), ∃ hρ : IsBlowupAlong m (f ⁻¹' C) ρ,
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (actualLift hf hπ hρ) ∧
      π ∘ actualLift hf hπ hρ = f ∘ ρ ∧
      GermIdeal.pullback (m := m) (actualLift hf hπ hρ)
        (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) =
        GermIdeal.pullback (m := m) ρ (vanishingIdeal (n := m) (f ⁻¹' C)) ∧
      (actualLift hf hπ hρ) ⁻¹' (π ⁻¹' C) = ρ ⁻¹' (f ⁻¹' C) := by
  obtain ⟨Z,ρ,hρ⟩ := exists_actual_source_blowup hf hπ
  exact ⟨Z,ρ,hρ,actualLift_isSubmersion hf hπ hρ,actualLift_proj_comm hf hπ hρ,
    actualLift_whole_ideal hf hπ hρ,actualLift_centre_preimage hf hπ hρ⟩
end AnyDimension

end
end Hironaka.HironakaSmoothSubmersionBlowupChoiceGeometry
