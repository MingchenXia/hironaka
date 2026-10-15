/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionBlowupPivotCompatibility
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionBlowupCartesian
open Hironaka.BlowupSequences BlowupTowers BlowupConstruction
  HironakaSmoothSubmersionBlowupLift HironakaSmoothSubmersionBlowupChoiceGeometry
  HironakaSmoothSubmersionBlowupLocalCones HironakaSmoothSubmersionBlowupPivotCompatibility
noncomputable section
variable {n m ℓ : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m} {P : CMfd.{u} ℓ}
  {f : Y → X} {C : Set X} {π : D → X} {π' : D' → Y}

def actualConeLift
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π')
    (u : P → Y) (v : P → D) (hsquare : ∀ p, π (v p) = f (u p)) : P → D' :=
  fun p => Classical.choose (existsUnique_actual_compatible_point hf hπ hπ' (u p) (v p) (hsquare p))

theorem actualConeLift_base
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π')
    (u : P → Y) (v : P → D) (hsquare : ∀ p, π (v p) = f (u p)) (p : P) :
    π' (actualConeLift hf hπ hπ' u v hsquare p) = u p :=
  (Classical.choose_spec (existsUnique_actual_compatible_point hf hπ hπ' (u p) (v p) (hsquare p))).1.1

theorem actualConeLift_image
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π')
    (u : P → Y) (v : P → D) (hsquare : ∀ p, π (v p) = f (u p)) (p : P) :
    actualLift hf hπ hπ' (actualConeLift hf hπ hπ' u v hsquare p) = v p :=
  (Classical.choose_spec (existsUnique_actual_compatible_point hf hπ hπ' (u p) (v p) (hsquare p))).1.2

theorem actualConeLift_contMDiff
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π')
    (u : P → Y) (v : P → D) (hsquare : ∀ p, π (v p) = f (u p))
    (hu : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ u)
    (hv : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ v) :
    ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ (actualConeLift hf hπ hπ' u v hsquare) := by
  intro p
  obtain ⟨W,hW,hp,g,hg,hgdict⟩ := exists_actual_local_cone hf hπ hπ' u v hu hv hsquare p
  have heq : EqOn (actualConeLift hf hπ hπ' u v hsquare) g W := by
    intro q hq
    obtain ⟨hb,hG⟩ := hgdict q hq
    exact actualLift_joint_unique hf hπ hπ' _ _
      ((actualConeLift_base hf hπ hπ' u v hsquare q).trans hb.symm)
      ((actualConeLift_image hf hπ hπ' u v hsquare q).trans hG.symm)
  exact ((hg p hp).contMDiffAt (hW.mem_nhds hp)).congr_of_eventuallyEq
    (heq.eventuallyEq_of_mem (hW.mem_nhds hp))

theorem existsUnique_actual_holomorphic_cone
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π')
    (u : P → Y) (v : P → D) (hsquare : ∀ p, π (v p) = f (u p))
    (hu : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ u)
    (hv : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ v) :
    ∃! g : P → D', ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ g ∧
      π' ∘ g = u ∧ actualLift hf hπ hπ' ∘ g = v := by
  refine ⟨actualConeLift hf hπ hπ' u v hsquare,
    ⟨actualConeLift_contMDiff hf hπ hπ' u v hsquare hu hv,?_,?_⟩,?_⟩
  · funext p; exact actualConeLift_base hf hπ hπ' u v hsquare p
  · funext p; exact actualConeLift_image hf hπ hπ' u v hsquare p
  · intro g hg
    funext p
    exact actualLift_joint_unique hf hπ hπ' _ _
      ((congrFun hg.2.1 p).trans (actualConeLift_base hf hπ hπ' u v hsquare p).symm)
      ((congrFun hg.2.2 p).trans (actualConeLift_image hf hπ hπ' u v hsquare p).symm)

theorem actualConeLift_comp {k : ℕ} {Q : CMfd.{u} k}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π')
    (u : P → Y) (v : P → D) (hsquare : ∀ p, π (v p) = f (u p)) (h : Q → P) :
    actualConeLift hf hπ hπ' (u ∘ h) (v ∘ h) (fun q => hsquare (h q)) =
      actualConeLift hf hπ hπ' u v hsquare ∘ h := by
  funext q
  exact actualLift_joint_unique hf hπ hπ' _ _
    ((actualConeLift_base hf hπ hπ' (u ∘ h) (v ∘ h) (fun q => hsquare (h q)) q).trans
      (actualConeLift_base hf hπ hπ' u v hsquare (h q)).symm)
    ((actualConeLift_image hf hπ hπ' (u ∘ h) (v ∘ h) (fun q => hsquare (h q)) q).trans
      (actualConeLift_image hf hπ hπ' u v hsquare (h q)).symm)


theorem exists_original_smooth_cartesian_blowup
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) :
    ∃ (Z : CMfd.{u} m) (ρ : Z → Y), ∃ hρ : IsBlowupAlong m (f ⁻¹' C) ρ,
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (actualLift hf hπ hρ) ∧
      π ∘ actualLift hf hπ hρ = f ∘ ρ ∧
      ∀ (k : ℕ) (Q : CMfd.{u} k) (u : Q → Y) (v : Q → D),
        ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel m) ∞ u →
        ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ v →
        (∀ q, π (v q) = f (u q)) →
        ∃! g : Q → Z, ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel m) ∞ g ∧
          ρ ∘ g = u ∧ actualLift hf hπ hρ ∘ g = v := by
  obtain ⟨Z,ρ,hρ⟩ := exists_actual_source_blowup hf hπ
  refine ⟨Z,ρ,hρ,actualLift_isSubmersion hf hπ hρ,actualLift_proj_comm hf hπ hρ,?_⟩
  intro k Q u v hu hv hsquare
  exact existsUnique_actual_holomorphic_cone hf hπ hρ u v hsquare hu hv

end
end Hironaka.HironakaSmoothSubmersionBlowupCartesian
