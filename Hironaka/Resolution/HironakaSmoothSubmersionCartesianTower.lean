/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionBlowupCartesian
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionCartesianTower
open Hironaka.BlowupSequences BlowupTowers BlowupConstruction
  HironakaSmoothSubmersionBlowupLift HironakaSmoothSubmersionBlowupChoiceGeometry
  HironakaSmoothSubmersionBlowupPivotCompatibility HironakaSmoothSubmersionBlowupCartesian
  HironakaSmoothSubmersionOrderedChoiceBaseChange
noncomputable section
variable {n m : ℕ}

/-- Output history with literal pulled centres and actual lifts, without surjectivity. -/
inductive IsActualTowerPullback {X : CMfd.{u} n} {Y : CMfd.{u} m} (f : Y → X) :
    {D' : CMfd.{u} m} → {D : CMfd.{u} n} → BlowupTower Y D' → BlowupTower X D →
      (D' → D) → Prop
  | refl (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
      IsActualTowerPullback f .refl .refl f
  | step {D' : CMfd.{u} m} {D : CMfd.{u} n} {Z' : CMfd.{u} m} {Z : CMfd.{u} n}
      {Q : BlowupTower Y D'} {T : BlowupTower X D} {g : D' → D}
      (h : IsActualTowerPullback f Q T g)
      (hg : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g)
      {C : Set D} {π : Z → D} (hπ : IsBlowupAlong n C π)
      {ρ : Z' → D'} (hρ : IsBlowupAlong m (g ⁻¹' C) ρ) :
      IsActualTowerPullback f (.step Q (g ⁻¹' C) ρ hρ) (.step T C π hπ)
        (actualLift hg hπ hρ)

theorem IsActualTowerPullback.isSubmersion {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
    {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g := by
  cases h with
  | refl hf => exact hf
  | step _ hg hπ hρ => exact actualLift_isSubmersion hg hπ hρ

theorem IsActualTowerPullback.length_eq {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
    {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) : Q.length = T.length := by
  induction h with
  | refl => rfl
  | step _ _ _ _ ih => exact congrArg (· + 1) ih

theorem IsActualTowerPullback.proj_comm {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
    {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) : ∀ x, T.proj (g x) = f (Q.proj x) := by
  induction h with
  | refl => exact fun _ => rfl
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    intro x
    change T.proj (π (actualLift hg hπ hρ x)) = f (Q.proj (ρ x))
    exact (congrArg T.proj (congrFun (actualLift_proj_comm hg hπ hρ) x)).trans (ih _)

theorem IsActualTowerPullback.universal {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
    {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) : HolomorphicSquarePullback f g Q.proj T.proj := by
  induction h with
  | refl =>
    intro ℓ P u v hu hv hcone
    refine ⟨u,⟨hu,fun _ => rfl,hcone⟩,?_⟩
    intro z hz
    funext p
    exact hz.2.1 p
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    intro ℓ P u v hu hv hcone
    obtain ⟨w₀,hw₀,huniq₀⟩ := ih ℓ P u (π ∘ v) hu (hπ.contMDiff.comp hv) hcone
    obtain ⟨w,hw,huniq⟩ := existsUnique_actual_holomorphic_cone hg hπ hρ w₀ v
      (fun x => (hw₀.2.2 x).symm) hw₀.1 hv
    refine ⟨w,⟨hw.1,?_,fun x => congrFun hw.2.2 x⟩,?_⟩
    · intro x
      change Q.proj (ρ (w x)) = u x
      exact (congrArg Q.proj (congrFun hw.2.1 x)).trans (hw₀.2.1 x)
    · intro z hz
      have hmid : (ρ ∘ z) = w₀ := huniq₀ _ ⟨hρ.contMDiff.comp hz.1,hz.2.1,by
        intro x
        change g (ρ (z x)) = π (v x)
        exact (congrFun (actualLift_proj_comm hg hπ hρ) (z x)).symm.trans
          (congrArg π (hz.2.2 x))⟩
      exact huniq z ⟨hz.1,hmid,funext hz.2.2⟩

theorem IsActualTowerPullback.head {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
    {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) (j : ℕ) :
    ∃ k : (BlowupTowerSplit.split Q j).1 → (BlowupTowerSplit.split T j).1,
      IsActualTowerPullback f (BlowupTowerSplit.head Q j) (BlowupTowerSplit.head T j) k := by
  induction h generalizing j with
  | refl hf => cases j <;> exact ⟨f,IsActualTowerPullback.refl hf⟩
  | step h hg hπ hρ ih =>
    cases j with
    | zero => exact ⟨actualLift hg hπ hρ,IsActualTowerPullback.step h hg hπ hρ⟩
    | succ j => exact ih j

theorem exists_actual_tower {X D : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (T : BlowupTower X D) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D), IsActualTowerPullback f Q T g := by
  induction T with
  | refl => exact ⟨Y,.refl,f,IsActualTowerPullback.refl hf⟩
  | step T C π hπ ih =>
    obtain ⟨D',Q,g,h⟩ := ih
    obtain ⟨Z',ρ,hρ⟩ := exists_actual_source_blowup h.isSubmersion hπ
    exact ⟨Z',.step Q (g ⁻¹' C) ρ hρ,actualLift h.isSubmersion hπ hρ,
      IsActualTowerPullback.step h h.isSubmersion hπ hρ⟩

theorem exists_original_smooth_cartesian_tower {X D : CMfd.{u} n} {Y : CMfd.{u} m}
    {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (T : BlowupTower X D) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g ∧
      Q.length = T.length ∧ (∀ x, T.proj (g x) = f (Q.proj x)) ∧
      HolomorphicSquarePullback f g Q.proj T.proj ∧
      ∀ j : ℕ, ∃ k : (BlowupTowerSplit.split Q j).1 → (BlowupTowerSplit.split T j).1,
        IsActualTowerPullback f (BlowupTowerSplit.head Q j) (BlowupTowerSplit.head T j) k ∧
        Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ k ∧
        (BlowupTowerSplit.head Q j).length = (BlowupTowerSplit.head T j).length ∧
        HolomorphicSquarePullback f k (BlowupTowerSplit.head Q j).proj
          (BlowupTowerSplit.head T j).proj := by
  obtain ⟨D',Q,g,h⟩ := exists_actual_tower hf T
  refine ⟨D',Q,g,h,h.isSubmersion,h.length_eq,h.proj_comm,h.universal,?_⟩
  intro j
  obtain ⟨k,hk⟩ := h.head j
  exact ⟨k,hk,hk.isSubmersion,hk.length_eq,hk.universal⟩

theorem IsActualTowerPullback.surjective {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
    {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) (hs : Function.Surjective f) : Function.Surjective g := by
  induction h with
  | refl => exact hs
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    intro z
    obtain ⟨y,hy⟩ := ih (π z)
    obtain ⟨p,hp,_⟩ := existsUnique_actual_compatible_point hg hπ hρ y z hy.symm
    exact ⟨p,hp.2⟩

theorem IsActualTowerPullback.to_surjective_history {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
    {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) (hs : Function.Surjective f) :
    IsSmoothTowerPullback f Q T g := by
  induction h with
  | refl hf => exact IsSmoothTowerPullback.refl hf hs
  | step h hg hπ hρ ih =>
    refine IsSmoothTowerPullback.step ih hρ hπ (actualLift hg hπ hρ)
      (actualLift_isSubmersion hg hπ hρ) ((IsActualTowerPullback.step h hg hπ hρ).surjective hs)
      (fun x => congrFun (actualLift_proj_comm hg hπ hρ) x) rfl ?_
    intro ℓ P u v hu hv hcone
    obtain ⟨w,hw,huniq⟩ := existsUnique_actual_holomorphic_cone hg hπ hρ u v
      (fun x => (hcone x).symm) hu hv
    refine ⟨w,⟨hw.1,fun x => congrFun hw.2.1 x,fun x => congrFun hw.2.2 x⟩,?_⟩
    intro z hz
    exact huniq z ⟨hz.1,funext hz.2.1,funext hz.2.2⟩

end
end Hironaka.HironakaSmoothSubmersionCartesianTower
