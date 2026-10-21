/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCylinderPullbackOrigin
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus

/-!
# Entire actual singular cylinder functional ideal pullback

True translations transport the whole original finite functional relations
and vanishing memberships. The original origin theorem then gives equality
of the independently defined functional ideals at EVERY actual point for
an arbitrary original subset. No coherence or desired equality is input.
Blueprint: `hironaka-actual-cylinder-pullback-points-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCylinderPullbackPoints
noncomputable section
open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  GermIdealPullbackCalculus HironakaRelativeNormalIdeal HironakaActualCylinderRelativeHadamard
  HironakaActualCylinderVanishingIdealExtension HironakaActualCylinderPullbackOrigin
variable {n : ℕ}

/-- Exactly the original generating functions composed with the genuine translation. -/
def translatedFamily (x : ComplexModel n) (S : (ComplexModel n → ℂ) → Prop) :
    (ComplexModel n → ℂ) → Prop := fun f => ∃ s,S s ∧ f=s∘(fun z => z+x)

/-- The actual shifted original set, with no germ or geometric presentation substituted. -/
def translatedSet (x : ComplexModel n) (W : Set (ComplexModel n)) : Set (ComplexModel n) :=
  {z | z+x∈W}

/-- Actual finite functional relations transport in BOTH directions under genuine original translations. -/
theorem isInSpanAt_translation_iff (x : ComplexModel n) (S : (ComplexModel n → ℂ) → Prop)
    (F : ComplexModel n → ℂ) :
    IsInSpanAt (n := n) S x F ↔
      IsInSpanAt (n := n) (translatedFamily x S) 0 (F∘(fun z => z+x)) := by
  have hp : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (fun z : ComplexModel n => z+x) := (show ContDiff ℂ ∞ _ from by fun_prop).contMDiff
  have hm : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (fun z : ComplexModel n => z-x) := (show ContDiff ℂ ∞ _ from by fun_prop).contMDiff
  constructor
  · intro hF
    exact isInSpanAt_comp hp (y := 0) (by simpa only [zero_add] using hF)
  · intro hF
    have hF' : IsInSpanAt (n := n) (translatedFamily x S) ((fun z : ComplexModel n => z-x) x)
        (F∘(fun z => z+x)) := by simpa only [sub_self] using hF
    have hc := isInSpanAt_comp hm hF'
    have ho : IsInSpanAt (n := n) S x ((F∘(fun z => z+x))∘(fun z => z-x)) := by
      refine IsInSpanAt.mono ?_ hc
      rintro _ ⟨a,⟨s,hs,rfl⟩,rfl⟩
      simpa only [Function.comp_def,sub_add_cancel] using hs
    simpa only [Function.comp_def,sub_add_cancel] using ho

/-- Original vanishing membership at any actual point equals original shifted vanishing membership at zero. -/
theorem vanishingIdeal_translation_iff (x : ComplexModel n) (W : Set (ComplexModel n))
    (F : ComplexModel n → ℂ) :
    (vanishingIdeal (n := n) W).mem x F ↔
      (vanishingIdeal (n := n) (translatedSet x W)).mem 0 (F∘(fun z => z+x)) := by
  have hp : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (fun z : ComplexModel n => z+x) := (show ContDiff ℂ ∞ _ from by fun_prop).contMDiff
  have hm : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (fun z : ComplexModel n => z-x) := (show ContDiff ℂ ∞ _ from by fun_prop).contMDiff
  constructor
  · intro hF
    have hh : HolomorphicAt n F ((fun z : ComplexModel n => z+x) 0) := by simpa using hF.1
    refine ⟨hh.comp_contMDiff (f := fun z : ComplexModel n => z+x) (Eventually.of_forall fun _ => hp.contMDiffAt),?_⟩
    have ht : Tendsto (fun z : ComplexModel n => z+x) (𝓝 0) (𝓝 x) := by
      simpa only [zero_add] using hp.continuous.tendsto 0
    have he := ht.eventually hF.2
    exact he.mono fun z hz hzW => hz hzW
  · intro hF
    have hh : HolomorphicAt n (F∘(fun z => z+x)) ((fun z : ComplexModel n => z-x) x) := by simpa using hF.1
    have hh' := hh.comp_contMDiff (f := fun z : ComplexModel n => z-x) (Eventually.of_forall fun _ => hm.contMDiffAt)
    have hhF : HolomorphicAt n F x := by simpa only [Function.comp_def,sub_add_cancel] using hh'
    refine ⟨hhF,?_⟩
    have ht : Tendsto (fun z : ComplexModel n => z-x) (𝓝 x) (𝓝 0) := by
      simpa only [sub_self] using hm.continuous.tendsto x
    filter_upwards [ht.eventually hF.2] with z hz hzW
    simpa only [Function.comp_def,sub_add_cancel] using hz (by simpa only [translatedSet,mem_ofPred_eq,sub_add_cancel] using hzW)

/-- The actual whole original composed-function family at the prescribed original point. -/
def pointPullbackFamily (k t : ℕ) (W : Set (ComplexModel k)) (x : ComplexModel (k+t)) :
    (ComplexModel (k+t) → ℂ) → Prop :=
  fun f => ∃ a : ComplexModel k → ℂ,(vanishingIdeal (n := k) W).mem (tangentProjection k t x) a ∧
    f=a∘tangentProjection k t

/-- ENTIRE original projection families, not just their supports, commute with genuine actual recentering. -/
theorem translated_pullback_family_eq (k t : ℕ) (W : Set (ComplexModel k)) (x : ComplexModel (k+t)) :
    translatedFamily x (pointPullbackFamily k t W x)=
      actualPullbackFunctionFamily k t (translatedSet (tangentProjection k t x) W) := by
  funext f
  apply propext
  constructor
  · rintro ⟨a,⟨b,hb,rfl⟩,rfl⟩
    refine ⟨b∘(fun y => y+tangentProjection k t x),
      (vanishingIdeal_translation_iff _ W b).mp hb,?_⟩
    funext z
    simp only [Function.comp_def,map_add]
  · rintro ⟨b,hb,rfl⟩
    let a : ComplexModel k → ℂ := fun y => b (y-tangentProjection k t x)
    have ha : (vanishingIdeal (n := k) W).mem (tangentProjection k t x) a := by
      apply (vanishingIdeal_translation_iff _ W a).mpr
      simpa only [a,Function.comp_def,add_sub_cancel_right] using hb
    refine ⟨a∘tangentProjection k t,⟨a,ha,rfl⟩,?_⟩
    funext z
    simp only [a,Function.comp_def,map_add,add_sub_cancel_right]

private theorem translated_cylinder_eq (k t : ℕ) (W : Set (ComplexModel k)) (x : ComplexModel (k+t)) :
    translatedSet x (cylinderCarrier k t W)=
      cylinderCarrier k t (translatedSet (tangentProjection k t x) W) := by
  ext z
  change tangentProjection k t (z+x)∈W ↔ tangentProjection k t z+tangentProjection k t x∈W
  rw [map_add]

/-- The independently defined original functional pullback equals original singular-product vanishing membership at EVERY actual point. -/
theorem pullback_vanishingIdeal_mem_iff (k t : ℕ) (W : Set (ComplexModel k))
    (x : ComplexModel (k+t)) (F : ComplexModel (k+t) → ℂ) :
    (GermIdeal.pullback (m := k+t) (tangentProjection k t) (vanishingIdeal (n := k) W)).mem x F ↔
      (vanishingIdeal (n := k+t) (cylinderCarrier k t W)).mem x F := by
  change IsInSpanAt (n := k+t) (pointPullbackFamily k t W x) x F ↔ _
  rw [isInSpanAt_translation_iff,translated_pullback_family_eq]
  change (GermIdeal.pullback (m := k+t) (tangentProjection k t)
    (vanishingIdeal (n := k) (translatedSet (tangentProjection k t x) W))).mem 0 (F∘(fun z => z+x)) ↔ _
  rw [pullback_vanishingIdeal_mem_zero_iff,← translated_cylinder_eq,
    ← vanishingIdeal_translation_iff]

/-- Equality of the ENTIRE independently defined original functional ideals for every original singular product. -/
theorem pullback_vanishingIdeal_eq (k t : ℕ) (W : Set (ComplexModel k)) :
    GermIdeal.pullback (m := k+t) (tangentProjection k t) (vanishingIdeal (n := k) W)=
      vanishingIdeal (n := k+t) (cylinderCarrier k t W) := by
  apply GermIdeal.ext
  funext x F
  exact propext (pullback_vanishingIdeal_mem_iff k t W x F)

end
end Hironaka.HironakaActualCylinderPullbackPoints
