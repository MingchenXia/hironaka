/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionMarkedCartesianTower
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionCartesianTowerChoiceComparison
open Hironaka.BlowupSequences BlowupTowers BlowupExistence
  MarkedIdeals MarkedIdeal HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionBlowupLift HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaSmoothSubmersionMarkedCartesianTower
  HironakaSmoothSubmersionOrderedChoiceImageTrace
noncomputable section
variable {n m : ℕ}

/-- Primitive choices contain only genuine individual geometric blowups. -/
structure SmoothBlowupChoices (m : ℕ) where
  choose {Y : CMfd.{u} m} {C : Set Y} (hC : IsClosedSubmanifold m C)
    (hCi : interior C = ∅) : Σ D : CMfd.{u} m, {ρ : D → Y // IsBlowupAlong m C ρ}

def defaultSmoothBlowupChoices : SmoothBlowupChoices.{u} m where
  choose hC hCi := by
    let hex := exists_isBlowupAlong _ hC hCi
    let Z := Classical.choose hex
    letI := Classical.choose (Classical.choose_spec hex)
    letI := Classical.choose (Classical.choose_spec (Classical.choose_spec hex))
    letI := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hex)))
    have hp := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hex)))
    exact ⟨CMfd.of (n := m) Z,Classical.choose hp,Classical.choose_spec hp⟩

/-- Actual source tower and stage history are produced from primitive choices. -/
def chosenActualTower {X : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
    (β : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {D : CMfd.{u} n} (T : BlowupTower X D) :
    Σ D' : CMfd.{u} m, Σ Q : BlowupTower Y D', {g : D' → D // IsActualTowerPullback f Q T g} := by
  induction T with
  | refl => exact ⟨Y,.refl,f,IsActualTowerPullback.refl hf⟩
  | step T C π hπ ih =>
    obtain ⟨D',Q,g,hg⟩ := ih
    have hC := actual_source_centre hg.isSubmersion hπ
    obtain ⟨Z',ρ,hρ⟩ := β.choose hC.1 hC.2
    exact ⟨Z',.step Q (g ⁻¹' C) ρ hρ,actualLift hg.isSubmersion hπ hρ,
      IsActualTowerPullback.step hg hg.isSubmersion hπ hρ⟩

theorem existsUnique_whole_cartesian_comparison {X D : CMfd.{u} n}
    {Y D₁ D₂ : CMfd.{u} m} {f : Y → X} {T : BlowupTower X D}
    {Q₁ : BlowupTower Y D₁} {Q₂ : BlowupTower Y D₂} {g₁ : D₁ → D} {g₂ : D₂ → D}
    (h₁ : IsActualTowerPullback f Q₁ T g₁) (h₂ : IsActualTowerPullback f Q₂ T g₂) :
    ∃! a : D₁ ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯ D₂,
      (∀ x, Q₂.proj (a x) = Q₁.proj x) ∧ (∀ x, g₂ (a x) = g₁ x) := by
  obtain ⟨a,ha,huniq⟩ := h₂.universal m D₁ Q₁.proj g₁ Q₁.contMDiff_proj
    h₁.isSubmersion.contMDiff (fun x => (h₁.proj_comm x).symm)
  obtain ⟨b,hb,_⟩ := h₁.universal m D₂ Q₂.proj g₂ Q₂.contMDiff_proj
    h₂.isSubmersion.contMDiff (fun x => (h₂.proj_comm x).symm)
  have hba : b ∘ a = id :=
    (h₁.universal m D₁ Q₁.proj g₁ Q₁.contMDiff_proj h₁.isSubmersion.contMDiff
      (fun x => (h₁.proj_comm x).symm)).unique
      ⟨hb.1.comp ha.1,fun x => (hb.2.1 (a x)).trans (ha.2.1 x),
        fun x => (hb.2.2 (a x)).trans (ha.2.2 x)⟩
      ⟨contMDiff_id,fun _ => rfl,fun _ => rfl⟩
  have hab : a ∘ b = id :=
    (h₂.universal m D₂ Q₂.proj g₂ Q₂.contMDiff_proj h₂.isSubmersion.contMDiff
      (fun x => (h₂.proj_comm x).symm)).unique
      ⟨ha.1.comp hb.1,fun x => (ha.2.1 (b x)).trans (hb.2.1 x),
        fun x => (ha.2.2 (b x)).trans (hb.2.2 x)⟩
      ⟨contMDiff_id,fun _ => rfl,fun _ => rfl⟩
  let φ : D₁ ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯ D₂ :=
    { toEquiv := ⟨a,b,fun x => congrFun hba x,fun x => congrFun hab x⟩
      contMDiff_toFun := ha.1
      contMDiff_invFun := hb.1 }
  refine ⟨φ,ha.2,?_⟩
  intro ψ hψ
  apply Diffeomorph.ext
  exact fun x => congrFun (huniq ψ ⟨ψ.contMDiff,hψ⟩) x

def choiceComparison {X D : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
    (β₁ β₂ : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (T : BlowupTower X D) :
    (chosenActualTower β₁ hf T).1 ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯
      (chosenActualTower β₂ hf T).1 :=
  Classical.choose (existsUnique_whole_cartesian_comparison
    (chosenActualTower β₁ hf T).2.2.property (chosenActualTower β₂ hf T).2.2.property)

theorem choiceComparison_source {X D : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
    (β₁ β₂ : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (T : BlowupTower X D) (x : (chosenActualTower β₁ hf T).1) :
    (chosenActualTower β₂ hf T).2.1.proj (choiceComparison β₁ β₂ hf T x) =
      (chosenActualTower β₁ hf T).2.1.proj x :=
  (Classical.choose_spec (existsUnique_whole_cartesian_comparison
    (chosenActualTower β₁ hf T).2.2.property (chosenActualTower β₂ hf T).2.2.property)).1.1 x

theorem choiceComparison_target {X D : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
    (β₁ β₂ : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (T : BlowupTower X D) (x : (chosenActualTower β₁ hf T).1) :
    (chosenActualTower β₂ hf T).2.2.val (choiceComparison β₁ β₂ hf T x) =
      (chosenActualTower β₁ hf T).2.2.val x :=
  (Classical.choose_spec (existsUnique_whole_cartesian_comparison
    (chosenActualTower β₁ hf T).2.2.property (chosenActualTower β₂ hf T).2.2.property)).1.2 x

theorem choiceComparison_unique {X D : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
    (β₁ β₂ : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (T : BlowupTower X D)
    (a : (chosenActualTower β₁ hf T).1 ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯
      (chosenActualTower β₂ hf T).1)
    (ha : ∀ x, (chosenActualTower β₂ hf T).2.1.proj (a x) =
      (chosenActualTower β₁ hf T).2.1.proj x)
    (hb : ∀ x, (chosenActualTower β₂ hf T).2.2.val (a x) =
      (chosenActualTower β₁ hf T).2.2.val x) : a = choiceComparison β₁ β₂ hf T :=
  (Classical.choose_spec (existsUnique_whole_cartesian_comparison
    (chosenActualTower β₁ hf T).2.2.property (chosenActualTower β₂ hf T).2.2.property)).2 a ⟨ha,hb⟩

theorem exists_original_choice_comparisons {X D : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
    (β₁ β₂ : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (T : BlowupTower X D) :
    let p := chosenActualTower β₁ hf T
    let q := chosenActualTower β₂ hf T
    p.2.1.length = T.length ∧ q.2.1.length = T.length ∧
    (∀ x, q.2.1.proj (choiceComparison β₁ β₂ hf T x) = p.2.1.proj x) ∧
    (∀ x, q.2.2.val (choiceComparison β₁ β₂ hf T x) = p.2.2.val x) ∧
    ∀ j : ℕ, ∃ (g₁ : (BlowupTowerSplit.split p.2.1 j).1 → (BlowupTowerSplit.split T j).1)
      (g₂ : (BlowupTowerSplit.split q.2.1 j).1 → (BlowupTowerSplit.split T j).1),
      IsActualTowerPullback f (BlowupTowerSplit.head p.2.1 j) (BlowupTowerSplit.head T j) g₁ ∧
      IsActualTowerPullback f (BlowupTowerSplit.head q.2.1 j) (BlowupTowerSplit.head T j) g₂ ∧
      ∃! a : (BlowupTowerSplit.split p.2.1 j).1
        ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯ (BlowupTowerSplit.split q.2.1 j).1,
        (∀ x, (BlowupTowerSplit.head q.2.1 j).proj (a x) =
          (BlowupTowerSplit.head p.2.1 j).proj x) ∧ (∀ x, g₂ (a x) = g₁ x) := by
  let p := chosenActualTower β₁ hf T
  let q := chosenActualTower β₂ hf T
  refine ⟨p.2.2.property.length_eq,q.2.2.property.length_eq,
    choiceComparison_source β₁ β₂ hf T,choiceComparison_target β₁ β₂ hf T,?_⟩
  intro j
  obtain ⟨g₁,h₁⟩ := p.2.2.property.head j
  obtain ⟨g₂,h₂⟩ := q.2.2.property.head j
  exact ⟨g₁,g₂,h₁,h₂,existsUnique_whole_cartesian_comparison h₁ h₂⟩

theorem choiceComparison_whole_marked {X D : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
    (β₁ β₂ : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    let p := chosenActualTower β₁ hf T
    let q := chosenActualTower β₂ hf T
    IsGeoTestTower (markedPullback (m := m) f M) p.2.1 ∧
    IsGeoTestTower (markedPullback (m := m) f M) q.2.1 ∧
    markedPullback (m := m) (choiceComparison β₁ β₂ hf T)
      (geoTransformAlong (markedPullback (m := m) f M) q.2.1) =
      geoTransformAlong (markedPullback (m := m) f M) p.2.1 := by
  let p := chosenActualTower β₁ hf T
  let q := chosenActualTower β₂ hf T
  obtain ⟨hP,hp⟩ := IsActualTowerPullback.fullAmbient_marked_dictionary p.2.2.property M hM hN hT
  obtain ⟨hQ,hq⟩ := IsActualTowerPullback.fullAmbient_marked_dictionary q.2.2.property M hM hN hT
  have hW := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT
  refine ⟨hP,hQ,?_⟩
  rw [hq,← whole_markedPullback_comp q.2.2.property.isSubmersion.contMDiff
    (choiceComparison β₁ β₂ hf T).contMDiff _ hW.isCoherent]
  have he : q.2.2.val ∘ choiceComparison β₁ β₂ hf T = p.2.2.val :=
    funext (choiceComparison_target β₁ β₂ hf T)
  rw [he]
  exact hp.symm

theorem choiceComparison_refl {X D : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
    (β : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (T : BlowupTower X D) :
    choiceComparison β β hf T = Diffeomorph.refl 𝓘(ℂ, ComplexModel m) _ ∞ :=
  (choiceComparison_unique β β hf T (Diffeomorph.refl _ _ ∞) (fun _ => rfl) (fun _ => rfl)).symm

theorem choiceComparison_cocycle {X D : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
    (β₁ β₂ β₃ : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (T : BlowupTower X D) :
    (choiceComparison β₁ β₂ hf T).trans (choiceComparison β₂ β₃ hf T) =
      choiceComparison β₁ β₃ hf T := by
  apply choiceComparison_unique
  · intro x
    exact (choiceComparison_source β₂ β₃ hf T (choiceComparison β₁ β₂ hf T x)).trans
      (choiceComparison_source β₁ β₂ hf T x)
  · intro x
    exact (choiceComparison_target β₂ β₃ hf T (choiceComparison β₁ β₂ hf T x)).trans
      (choiceComparison_target β₁ β₂ hf T x)

end
end Hironaka.HironakaSmoothSubmersionCartesianTowerChoiceComparison
