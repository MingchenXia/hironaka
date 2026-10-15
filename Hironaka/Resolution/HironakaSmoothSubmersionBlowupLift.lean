/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeRestriction
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceImageTrace
import Hironaka.Blowup.BlowupExistence
import Hironaka.Blowup.BlowupUniqueness
import Hironaka.Resolution.HironakaBlowupComparisonCocycle

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionBlowupLift
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers
  HironakaSmoothSubmersionRelativeRestriction HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionOrderedImageTrace HironakaSmoothSubmersionOrderedChoiceImageTrace
  VanishingIdealCoherent BlowupExistence
noncomputable section
variable {n m : ℕ} {A D : CMfd.{u} n} {B : CMfd.{u} m}
  {f : B → A} {C : Set A} {π : D → A}

/-- Original geometry internally gives the true pulled closed/nowhere-dense source centre. -/
theorem actual_source_centre
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) :
    IsClosedSubmanifold m (f ⁻¹' C) ∧ interior (f ⁻¹' C) = ∅ := by
  refine ⟨isClosedSubmanifold_preimage_submersion hf hπ.1,?_⟩
  rw [← (isOpenMap_of_isSubmersion hf).preimage_interior_eq_interior_preimage hf.contMDiff.continuous,
    hπ.2.1,preimage_empty]

/-- ONLY original f and the actual target blowup produce a genuine source blowup internally. -/
theorem exists_actual_source_blowup
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) :
    ∃ (D' : CMfd.{u} m) (π' : D' → B), IsBlowupAlong m (f ⁻¹' C) π' := by
  obtain ⟨hC,hCi⟩ := actual_source_centre hf hπ
  obtain ⟨Z,t,c,h,π',hπ'⟩ := exists_isBlowupAlong (f ⁻¹' C) hC hCi
  let _ := t
  let _ := c
  let _ := h
  exact ⟨CMfd.of (n := m) Z,π',hπ'⟩

/-- The SAME entire actual original ideal has the true source blowup pullback. -/
theorem actual_base_ideal_eq {D' : CMfd.{u} m} {π' : D' → B}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π') :
    GermIdeal.pullback (m := m) (f ∘ π') (vanishingIdeal (n := n) C) =
      GermIdeal.pullback (m := m) π' (vanishingIdeal (n := m) (f ⁻¹' C)) := by
  rw [coherent_pullback_comp hf.contMDiff hπ'.contMDiff _ (isCoherent_vanishingIdeal hπ.1),
    pullback_vanishingIdeal_submersion hf hπ.1]

/-- Invertibility is genuinely supplied by this actual source blowup, never arbitrary pullback stability. -/
theorem actual_base_ideal_invertible {D' : CMfd.{u} m} {π' : D' → B}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π') :
    (GermIdeal.pullback (m := m) (f ∘ π') (vanishingIdeal (n := n) C)).IsInvertible := by
  rw [actual_base_ideal_eq hf hπ hπ']
  exact hπ'.2.2.2.1

/-- Ordinary genuine source/target blowup choices internally produce their unique holomorphic lift. -/
theorem existsUnique_actual_lift {D' : CMfd.{u} m} {π' : D' → B}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π') :
    ∃! g : D' → D, ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g ∧
      π ∘ g = f ∘ π' :=
  hπ.2.2.2.2 m D' (f ∘ π') (hf.contMDiff.comp hπ'.contMDiff)
    (actual_base_ideal_invertible hf hπ hπ')

/-- This map is the true uniquely produced original geometric lift. -/
def actualLift {D' : CMfd.{u} m} {π' : D' → B}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π') : D' → D :=
  Classical.choose (existsUnique_actual_lift hf hπ hπ')

theorem actualLift_contMDiff {D' : CMfd.{u} m} {π' : D' → B}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π') :
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (actualLift hf hπ hπ') :=
  (Classical.choose_spec (existsUnique_actual_lift hf hπ hπ')).1.1

theorem actualLift_proj_comm {D' : CMfd.{u} m} {π' : D' → B}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π') :
    π ∘ actualLift hf hπ hπ' = f ∘ π' :=
  (Classical.choose_spec (existsUnique_actual_lift hf hπ hπ')).1.2

theorem actualLift_unique {D' : CMfd.{u} m} {π' : D' → B}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π') (g : D' → D)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hc : π ∘ g = f ∘ π') : g = actualLift hf hπ hπ' :=
  (Classical.choose_spec (existsUnique_actual_lift hf hπ hπ')).2 g ⟨hg,hc⟩

/-- ENTIRE original target blowup ideal equals the literal source blowup ideal under the actual lift. -/
theorem actualLift_whole_ideal {D' : CMfd.{u} m} {π' : D' → B}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π') :
    GermIdeal.pullback (m := m) (actualLift hf hπ hπ')
      (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) =
    GermIdeal.pullback (m := m) π' (vanishingIdeal (n := m) (f ⁻¹' C)) := by
  rw [← coherent_pullback_comp hπ.contMDiff (actualLift_contMDiff hf hπ hπ') _
    (isCoherent_vanishingIdeal hπ.1),actualLift_proj_comm hf hπ hπ',actual_base_ideal_eq hf hπ hπ']

/-- Actual centre-preimage divisors agree; no differential exceptional-locus identification is claimed. -/
theorem actualLift_centre_preimage {D' : CMfd.{u} m} {π' : D' → B}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π') :
    (actualLift hf hπ hπ') ⁻¹' (π ⁻¹' C) = π' ⁻¹' (f ⁻¹' C) := by
  rw [← preimage_comp,actualLift_proj_comm hf hπ hπ',preimage_comp]

/-- Actual produced output only; never an input to any original-geometry consumer. -/
structure ActualBlowupLift (f : B → A) (C : Set A) (π : D → A) where
  source : CMfd.{u} m
  projection : source → B
  isBlowupAlong : IsBlowupAlong m (f ⁻¹' C) projection
  lift : source → D
  holomorphic : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ lift
  square : π ∘ lift = f ∘ projection
  wholeIdeal : GermIdeal.pullback (m := m) lift (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) =
    GermIdeal.pullback (m := m) projection (vanishingIdeal (n := m) (f ⁻¹' C))
  centrePreimage : lift ⁻¹' (π ⁻¹' C) = projection ⁻¹' (f ⁻¹' C)

/-- ONLY original submersion and genuine target blowup construct the whole real lift output. -/
theorem exists_actualBlowupLift
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) : Nonempty (ActualBlowupLift f C π) := by
  obtain ⟨D',π',hπ'⟩ := exists_actual_source_blowup hf hπ
  exact ⟨⟨D',π',hπ',actualLift hf hπ hπ',actualLift_contMDiff hf hπ hπ',
    actualLift_proj_comm hf hπ hπ',actualLift_whole_ideal hf hπ hπ',actualLift_centre_preimage hf hπ hπ'⟩⟩

/-- Genuine entire source/target choice families internally give ALL lift squares and true cocycles. -/
theorem exists_choice_lift_cocycles {I J : Type*}
    (Y : I → CMfd.{u} n) (Z : J → CMfd.{u} m)
    (p : ∀ i, Y i → A) (q : ∀ j, Z j → B)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hp : ∀ i, IsBlowupAlong n C (p i))
    (hq : ∀ j, IsBlowupAlong m (f ⁻¹' C) (q j)) :
    ∃ Φ : ∀ i i', Y i ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y i',
      (∀ i i', p i' ∘ Φ i i' = p i) ∧
      (∀ i, (Φ i i : Y i → Y i) = id) ∧
      (∀ i i' i'', (Φ i' i'' : Y i' → Y i'') ∘ (Φ i i' : Y i → Y i') = Φ i i'') ∧
      (∀ i i', (Φ i i').symm.toEquiv.toFun = (Φ i' i).toEquiv.toFun) ∧
    ∃ Ψ : ∀ j j', Z j ≃ₘ⟮𝓘(ℂ, ComplexModel m), 𝓘(ℂ, ComplexModel m)⟯ Z j',
      (∀ j j', q j' ∘ Ψ j j' = q j) ∧
      (∀ j, (Ψ j j : Z j → Z j) = id) ∧
      (∀ j j' j'', (Ψ j' j'' : Z j' → Z j'') ∘ (Ψ j j' : Z j → Z j') = Ψ j j'') ∧
      (∀ j j', (Ψ j j').symm.toEquiv.toFun = (Ψ j' j).toEquiv.toFun) ∧
      ∀ i i' j j', (Φ i i' : Y i → Y i') ∘ actualLift hf (hp i) (hq j) =
        actualLift hf (hp i') (hq j') ∘ (Ψ j j' : Z j → Z j') := by
  obtain ⟨Φ,hΦ,hΦid,hΦcomp,hΦinv⟩ :=
    HironakaBlowupComparisonCocycle.exists_biholomorphism_cocycle Y p hp
  obtain ⟨Ψ,hΨ,hΨid,hΨcomp,hΨinv⟩ :=
    HironakaBlowupComparisonCocycle.exists_biholomorphism_cocycle Z q hq
  refine ⟨Φ,hΦ,hΦid,hΦcomp,hΦinv,Ψ,hΨ,hΨid,hΨcomp,hΨinv,?_⟩
  intro i i' j j'
  have hleft := actualLift_unique hf (hp i') (hq j)
    ((Φ i i' : Y i → Y i') ∘ actualLift hf (hp i) (hq j))
    ((Φ i i').contMDiff.comp (actualLift_contMDiff hf (hp i) (hq j)))
    (by rw [← Function.comp_assoc,hΦ,actualLift_proj_comm])
  have hright := actualLift_unique hf (hp i') (hq j)
    (actualLift hf (hp i') (hq j') ∘ (Ψ j j' : Z j → Z j'))
    ((actualLift_contMDiff hf (hp i') (hq j')).comp (Ψ j j').contMDiff)
    (by rw [← Function.comp_assoc,actualLift_proj_comm,Function.comp_assoc,hΨ])
  exact hleft.trans hright.symm

variable {ℓ : ℕ} {P Q : CMfd.{u} ℓ} {h : P → B} {ρ : Q → P}

/-- TWO original submersions, without a composite-submersion certificate, give the entire base ideal. -/
theorem actual_composite_base_ideal_eq
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (hπ : IsBlowupAlong n C π)
    (hρ : IsBlowupAlong ℓ (h ⁻¹' (f ⁻¹' C)) ρ) :
    GermIdeal.pullback (m := ℓ) ((f ∘ h) ∘ ρ) (vanishingIdeal (n := n) C) =
      GermIdeal.pullback (m := ℓ) ρ (vanishingIdeal (n := ℓ) (h ⁻¹' (f ⁻¹' C))) := by
  rw [coherent_pullback_comp (hf.contMDiff.comp hh.contMDiff) hρ.contMDiff _
    (isCoherent_vanishingIdeal hπ.1),
    coherent_pullback_comp hf.contMDiff hh.contMDiff _ (isCoherent_vanishingIdeal hπ.1),
    pullback_vanishingIdeal_submersion hf hπ.1,
    pullback_vanishingIdeal_submersion hh (actual_source_centre hf hπ).1]

/-- Original two-map geometry and the genuine final source blowup produce a unique direct lift. -/
theorem existsUnique_actual_composite_lift
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (hπ : IsBlowupAlong n C π)
    (hρ : IsBlowupAlong ℓ (h ⁻¹' (f ⁻¹' C)) ρ) :
    ∃! g : Q → D, ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ g ∧
      π ∘ g = (f ∘ h) ∘ ρ := by
  apply hπ.2.2.2.2 ℓ Q ((f ∘ h) ∘ ρ)
    ((hf.contMDiff.comp hh.contMDiff).comp hρ.contMDiff)
  rw [actual_composite_base_ideal_eq hf hh hπ hρ]
  exact hρ.2.2.2.1

/-- The actual direct two-original-map lift is chosen from true universal uniqueness. -/
def actualCompositeLift
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (hπ : IsBlowupAlong n C π)
    (hρ : IsBlowupAlong ℓ (h ⁻¹' (f ⁻¹' C)) ρ) : Q → D :=
  Classical.choose (existsUnique_actual_composite_lift hf hh hπ hρ)

theorem actualCompositeLift_contMDiff
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (hπ : IsBlowupAlong n C π)
    (hρ : IsBlowupAlong ℓ (h ⁻¹' (f ⁻¹' C)) ρ) :
    ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ (actualCompositeLift hf hh hπ hρ) :=
  (Classical.choose_spec (existsUnique_actual_composite_lift hf hh hπ hρ)).1.1

theorem actualCompositeLift_proj_comm
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (hπ : IsBlowupAlong n C π)
    (hρ : IsBlowupAlong ℓ (h ⁻¹' (f ⁻¹' C)) ρ) :
    π ∘ actualCompositeLift hf hh hπ hρ = (f ∘ h) ∘ ρ :=
  (Classical.choose_spec (existsUnique_actual_composite_lift hf hh hπ hρ)).1.2

/-- The actual successive lift composite equals the independently produced direct lift. -/
theorem actualCompositeLift_eq_comp {D' : CMfd.{u} m} {π' : D' → B}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π')
    (hρ : IsBlowupAlong ℓ (h ⁻¹' (f ⁻¹' C)) ρ) :
    actualCompositeLift hf hh hπ hρ = actualLift hf hπ hπ' ∘ actualLift hh hπ' hρ := by
  apply ((Classical.choose_spec (existsUnique_actual_composite_lift hf hh hπ hρ)).2
    (actualLift hf hπ hπ' ∘ actualLift hh hπ' hρ) ⟨?_,?_⟩).symm
  · exact (actualLift_contMDiff hf hπ hπ').comp (actualLift_contMDiff hh hπ' hρ)
  · rw [← Function.comp_assoc,actualLift_proj_comm,Function.comp_assoc,actualLift_proj_comm]
    rfl

/-- The direct lift has the ENTIRE literal final-source blowup ideal. -/
theorem actualCompositeLift_whole_ideal
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (hπ : IsBlowupAlong n C π)
    (hρ : IsBlowupAlong ℓ (h ⁻¹' (f ⁻¹' C)) ρ) :
    GermIdeal.pullback (m := ℓ) (actualCompositeLift hf hh hπ hρ)
      (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) =
    GermIdeal.pullback (m := ℓ) ρ (vanishingIdeal (n := ℓ) (h ⁻¹' (f ⁻¹' C))) := by
  rw [← coherent_pullback_comp hπ.contMDiff (actualCompositeLift_contMDiff hf hh hπ hρ) _
    (isCoherent_vanishingIdeal hπ.1),actualCompositeLift_proj_comm,
    actual_composite_base_ideal_eq hf hh hπ hρ]

/-- The actual final source centre is literally the composite original preimage. -/
theorem actualCompositeLift_centre_preimage
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (hπ : IsBlowupAlong n C π)
    (hρ : IsBlowupAlong ℓ (h ⁻¹' (f ⁻¹' C)) ρ) :
    (actualCompositeLift hf hh hπ hρ) ⁻¹' (π ⁻¹' C) = ρ ⁻¹' ((f ∘ h) ⁻¹' C) := by
  rw [← preimage_comp,actualCompositeLift_proj_comm,preimage_comp]

/-- Original geometry constructs BOTH successive true source blowups, with no caller source choice. -/
theorem exists_actual_successive_blowups
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (hπ : IsBlowupAlong n C π) :
    ∃ (D' : CMfd.{u} m) (π' : D' → B),
      IsBlowupAlong m (f ⁻¹' C) π' ∧
      ∃ (Q' : CMfd.{u} ℓ) (ρ' : Q' → P), IsBlowupAlong ℓ (h ⁻¹' (f ⁻¹' C)) ρ' := by
  obtain ⟨D',π',hπ'⟩ := exists_actual_source_blowup hf hπ
  obtain ⟨Q',ρ',hρ'⟩ := exists_actual_source_blowup hh hπ'
  exact ⟨D',π',hπ',Q',ρ',hρ'⟩

/-- ONLY original two-submersion geometry constructs both source choices and the genuine composite square. -/
theorem exists_actual_successive_lifts
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (hπ : IsBlowupAlong n C π) :
    ∃ (D' : CMfd.{u} m) (π' : D' → B) (hπ' : IsBlowupAlong m (f ⁻¹' C) π')
      (Q' : CMfd.{u} ℓ) (ρ' : Q' → P) (hρ' : IsBlowupAlong ℓ (h ⁻¹' (f ⁻¹' C)) ρ'),
      actualCompositeLift hf hh hπ hρ' = actualLift hf hπ hπ' ∘ actualLift hh hπ' hρ' ∧
      π ∘ actualCompositeLift hf hh hπ hρ' = (f ∘ h) ∘ ρ' ∧
      GermIdeal.pullback (m := ℓ) (actualCompositeLift hf hh hπ hρ')
        (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) =
      GermIdeal.pullback (m := ℓ) ρ' (vanishingIdeal (n := ℓ) (h ⁻¹' (f ⁻¹' C))) := by
  obtain ⟨D',π',hπ',Q',ρ',hρ'⟩ := exists_actual_successive_blowups hf hh hπ
  exact ⟨D',π',hπ',Q',ρ',hρ',actualCompositeLift_eq_comp hf hh hπ hπ' hρ',
    actualCompositeLift_proj_comm hf hh hπ hρ',actualCompositeLift_whole_ideal hf hh hπ hρ'⟩

end
end Hironaka.HironakaSmoothSubmersionBlowupLift
