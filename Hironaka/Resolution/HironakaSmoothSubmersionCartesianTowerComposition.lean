/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionCartesianTowerChoiceComparison
import Hironaka.Resolution.HironakaSmoothSubmersionComposition
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionCartesianTowerComposition
open Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeal
  HironakaSmoothSubmersionBlowupLift HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCartesianTowerChoiceComparison HironakaSmoothSubmersionComposition
  HironakaSmoothSubmersionMarkedCartesianTower HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
noncomputable section
variable {n m ℓ : ℕ}

theorem actualLift_two_submersions {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
    {Z D'' : CMfd.{u} ℓ} {f : Y → X} {h : Z → Y} {C : Set X}
    {π : D → X} {ρ : D' → Y} {τ : D'' → Z}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong m (f ⁻¹' C) ρ)
    (hτ : IsBlowupAlong ℓ (h ⁻¹' (f ⁻¹' C)) τ) :
    actualLift (isSubmersion_composition hf hh) hπ hτ =
      actualLift hf hπ hρ ∘ actualLift hh hρ hτ := by
  apply (actualLift_unique (isSubmersion_composition hf hh) hπ hτ _
    ((actualLift_contMDiff hf hπ hρ).comp (actualLift_contMDiff hh hρ hτ)) ?_).symm
  funext x
  exact (congrFun (actualLift_proj_comm hf hπ hρ) (actualLift hh hρ hτ x)).trans
    (congrArg f (congrFun (actualLift_proj_comm hh hρ hτ) x))

theorem IsActualTowerPullback.comp {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
    {Z D'' : CMfd.{u} ℓ} {f : Y → X} {h : Z → Y} {g₁ : D' → D} {g₂ : D'' → D'}
    {T : BlowupTower X D} {Q : BlowupTower Y D'} {R : BlowupTower Z D''}
    (h₁ : IsActualTowerPullback f Q T g₁) (h₂ : IsActualTowerPullback h R Q g₂) :
    IsActualTowerPullback (f ∘ h) R T (g₁ ∘ g₂) := by
  revert h₁
  induction h₂ generalizing D T with
  | refl hh =>
    intro h₁
    cases h₁ with
    | refl hf => exact IsActualTowerPullback.refl (isSubmersion_composition hf hh)
  | step h₂ hg₂ hπ' hτ ih =>
    intro h₁
    cases h₁ with
    | step h₁ hg₁ hπ hρ =>
      rw [← actualLift_two_submersions hg₁ hg₂ hπ hρ hτ]
      exact IsActualTowerPullback.step (ih h₁) (isSubmersion_composition hg₁ hg₂) hπ hτ

def compositionSource {X D : CMfd.{u} n} {Y : CMfd.{u} m} {Z : CMfd.{u} ℓ}
    {f : Y → X} {h : Z → Y} (β : SmoothBlowupChoices.{u} m) (γ : SmoothBlowupChoices.{u} ℓ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (T : BlowupTower X D) :
    Σ D'' : CMfd.{u} ℓ, Σ R : BlowupTower Z D'',
      {g : D'' → D // IsActualTowerPullback (f ∘ h) R T g} :=
  let q := chosenActualTower β hf T
  let r := chosenActualTower γ hh q.2.1
  ⟨r.1,r.2.1,q.2.2.val ∘ r.2.2.val,IsActualTowerPullback.comp q.2.2.property r.2.2.property⟩

def compositionComparison {X D : CMfd.{u} n} {Y : CMfd.{u} m} {Z : CMfd.{u} ℓ}
    {f : Y → X} {h : Z → Y}
    (β : SmoothBlowupChoices.{u} m) (γ δ : SmoothBlowupChoices.{u} ℓ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (T : BlowupTower X D) :
    (compositionSource β γ hf hh T).1 ≃ₘ⟮𝓘(ℂ, ComplexModel ℓ),𝓘(ℂ, ComplexModel ℓ)⟯
      (chosenActualTower δ (isSubmersion_composition hf hh) T).1 :=
  Classical.choose (existsUnique_whole_cartesian_comparison
    (compositionSource β γ hf hh T).2.2.property
    (chosenActualTower δ (isSubmersion_composition hf hh) T).2.2.property)

theorem compositionComparison_source {X D : CMfd.{u} n} {Y : CMfd.{u} m} {Z : CMfd.{u} ℓ}
    {f : Y → X} {h : Z → Y}
    (β : SmoothBlowupChoices.{u} m) (γ δ : SmoothBlowupChoices.{u} ℓ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (T : BlowupTower X D) (x : (compositionSource β γ hf hh T).1) :
    (chosenActualTower δ (isSubmersion_composition hf hh) T).2.1.proj
      (compositionComparison β γ δ hf hh T x) = (compositionSource β γ hf hh T).2.1.proj x :=
  (Classical.choose_spec (existsUnique_whole_cartesian_comparison
    (compositionSource β γ hf hh T).2.2.property
    (chosenActualTower δ (isSubmersion_composition hf hh) T).2.2.property)).1.1 x

theorem compositionComparison_target {X D : CMfd.{u} n} {Y : CMfd.{u} m} {Z : CMfd.{u} ℓ}
    {f : Y → X} {h : Z → Y}
    (β : SmoothBlowupChoices.{u} m) (γ δ : SmoothBlowupChoices.{u} ℓ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (T : BlowupTower X D) (x : (compositionSource β γ hf hh T).1) :
    (chosenActualTower δ (isSubmersion_composition hf hh) T).2.2.val
      (compositionComparison β γ δ hf hh T x) = (compositionSource β γ hf hh T).2.2.val x :=
  (Classical.choose_spec (existsUnique_whole_cartesian_comparison
    (compositionSource β γ hf hh T).2.2.property
    (chosenActualTower δ (isSubmersion_composition hf hh) T).2.2.property)).1.2 x

theorem compositionComparison_unique {X D : CMfd.{u} n} {Y : CMfd.{u} m} {Z : CMfd.{u} ℓ}
    {f : Y → X} {h : Z → Y}
    (β : SmoothBlowupChoices.{u} m) (γ δ : SmoothBlowupChoices.{u} ℓ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (T : BlowupTower X D)
    (a : (compositionSource β γ hf hh T).1 ≃ₘ⟮𝓘(ℂ, ComplexModel ℓ),𝓘(ℂ, ComplexModel ℓ)⟯
      (chosenActualTower δ (isSubmersion_composition hf hh) T).1)
    (ha : ∀ x, (chosenActualTower δ (isSubmersion_composition hf hh) T).2.1.proj (a x) =
      (compositionSource β γ hf hh T).2.1.proj x)
    (hb : ∀ x, (chosenActualTower δ (isSubmersion_composition hf hh) T).2.2.val (a x) =
      (compositionSource β γ hf hh T).2.2.val x) : a = compositionComparison β γ δ hf hh T :=
  (Classical.choose_spec (existsUnique_whole_cartesian_comparison
    (compositionSource β γ hf hh T).2.2.property
    (chosenActualTower δ (isSubmersion_composition hf hh) T).2.2.property)).2 a ⟨ha,hb⟩

theorem exists_original_composition_comparisons {X D : CMfd.{u} n} {Y : CMfd.{u} m}
    {Z : CMfd.{u} ℓ} {f : Y → X} {h : Z → Y}
    (β : SmoothBlowupChoices.{u} m) (γ δ : SmoothBlowupChoices.{u} ℓ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (T : BlowupTower X D) :
    let p := compositionSource β γ hf hh T
    let q := chosenActualTower δ (isSubmersion_composition hf hh) T
    p.2.1.length = T.length ∧ q.2.1.length = T.length ∧
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ p.2.2.val ∧
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ q.2.2.val ∧
    HolomorphicSquarePullback (f ∘ h) p.2.2.val p.2.1.proj T.proj ∧
    HolomorphicSquarePullback (f ∘ h) q.2.2.val q.2.1.proj T.proj ∧
    ∀ j : ℕ, ∃ (g₁ : (BlowupTowerSplit.split p.2.1 j).1 → (BlowupTowerSplit.split T j).1)
      (g₂ : (BlowupTowerSplit.split q.2.1 j).1 → (BlowupTowerSplit.split T j).1),
      IsActualTowerPullback (f ∘ h) (BlowupTowerSplit.head p.2.1 j) (BlowupTowerSplit.head T j) g₁ ∧
      IsActualTowerPullback (f ∘ h) (BlowupTowerSplit.head q.2.1 j) (BlowupTowerSplit.head T j) g₂ ∧
      ∃! a : (BlowupTowerSplit.split p.2.1 j).1
        ≃ₘ⟮𝓘(ℂ, ComplexModel ℓ),𝓘(ℂ, ComplexModel ℓ)⟯ (BlowupTowerSplit.split q.2.1 j).1,
        (∀ x, (BlowupTowerSplit.head q.2.1 j).proj (a x) =
          (BlowupTowerSplit.head p.2.1 j).proj x) ∧ (∀ x, g₂ (a x) = g₁ x) := by
  let p := compositionSource β γ hf hh T
  let q := chosenActualTower δ (isSubmersion_composition hf hh) T
  refine ⟨p.2.2.property.length_eq,q.2.2.property.length_eq,
    p.2.2.property.isSubmersion,q.2.2.property.isSubmersion,
    p.2.2.property.universal,q.2.2.property.universal,?_⟩
  intro j
  obtain ⟨g₁,h₁⟩ := p.2.2.property.head j
  obtain ⟨g₂,h₂⟩ := q.2.2.property.head j
  exact ⟨g₁,g₂,h₁,h₂,existsUnique_whole_cartesian_comparison h₁ h₂⟩

theorem compositionComparison_whole_marked {X D : CMfd.{u} n} {Y : CMfd.{u} m}
    {Z : CMfd.{u} ℓ} {f : Y → X} {h : Z → Y}
    (β : SmoothBlowupChoices.{u} m) (γ δ : SmoothBlowupChoices.{u} ℓ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    let p := compositionSource β γ hf hh T
    let q := chosenActualTower δ (isSubmersion_composition hf hh) T
    IsGeoTestTower (markedPullback (m := ℓ) h (markedPullback (m := m) f M)) p.2.1 ∧
    IsGeoTestTower (markedPullback (m := ℓ) (f ∘ h) M) q.2.1 ∧
    markedPullback (m := ℓ) (compositionComparison β γ δ hf hh T)
      (geoTransformAlong (markedPullback (m := ℓ) (f ∘ h) M) q.2.1) =
      geoTransformAlong (markedPullback (m := ℓ) h (markedPullback (m := m) f M)) p.2.1 := by
  let p := compositionSource β γ hf hh T
  let q := chosenActualTower δ (isSubmersion_composition hf hh) T
  obtain ⟨hP,hp⟩ := IsActualTowerPullback.fullAmbient_marked_dictionary p.2.2.property M hM hN hT
  obtain ⟨hQ,hq⟩ := IsActualTowerPullback.fullAmbient_marked_dictionary q.2.2.property M hM hN hT
  have hW := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT
  have hinit := whole_markedPullback_comp hf.contMDiff hh.contMDiff M hM.isCoherent
  refine ⟨?_,hQ,?_⟩
  · rw [← hinit]
    exact hP
  · rw [← hinit,hq,← whole_markedPullback_comp q.2.2.property.isSubmersion.contMDiff
      (compositionComparison β γ δ hf hh T).contMDiff _ hW.isCoherent]
    have he : q.2.2.val ∘ compositionComparison β γ δ hf hh T = p.2.2.val :=
      funext (compositionComparison_target β γ δ hf hh T)
    rw [he]
    exact hp.symm

end
end Hironaka.HironakaSmoothSubmersionCartesianTowerComposition
