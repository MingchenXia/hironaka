/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionNonmonomialHistory
import Hironaka.Resolution.HironakaSmoothSubmersionContactParameterCoefficientIdeals
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionHistoricalCompanionMasks
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec InvDomainTowerAlong
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionRelativePartsCompanion HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionNonmonomialHistory
  HironakaSmoothSubmersionContactParameterCharts HironakaSmoothSubmersionContactParameterCoefficientIdeals
  NonmonomialOrderTail CompanionRebase GeneralValue HironakaGeneralThreeNonspecialAnalyticLoci
noncomputable section
variable {n m k : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

theorem IsActualTowerPullback.simultaneous_split
    (h : IsActualTowerPullback f Q T g) (j : ℕ) :
    ∃ a : (split Q j).1 → (split T j).1,
      IsActualTowerPullback f (head Q j) (head T j) a ∧
      IsActualTowerPullback a (tail Q j) (tail T j) g := by
  induction h generalizing j with
  | refl hf => cases j <;> exact ⟨f,IsActualTowerPullback.refl hf,IsActualTowerPullback.refl hf⟩
  | step h hg hπ hρ ih =>
    cases j with
    | zero => exact ⟨_,IsActualTowerPullback.step h hg hπ hρ,
        IsActualTowerPullback.refl (IsActualTowerPullback.step h hg hπ hρ).isSubmersion⟩
    | succ j =>
      obtain ⟨a,hhead,htail⟩ := ih j
      exact ⟨a,hhead,IsActualTowerPullback.step htail hg hπ hρ⟩

theorem IsActualTowerPullback.order_mask_dictionary (hn : 0 < n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (o : ℕ) :
    (ordMask (geoTransformAlong (markedPullback (m := m) f M) Q) o : Set D') =
      g ⁻¹' (ordMask (geoTransformAlong M T) o : Set D) := by
  have hc := isInvDomain_geoTransformAlong hM T hT
  rw [(IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hT).2]
  exact ordMask_markedPullback h.isSubmersion hn _ hc.isWellFormed hc.isNonzeroAlongAt o

theorem restrictedOpenMap_isSubmersion
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (V : TopologicalSpace.Opens Y) (U : TopologicalSpace.Opens X) (hVU : MapsTo f V U) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞
      (restrictedOpenMap V U hVU) :=
  (restrictedOpenMap_isSubmersionOfComplement hf.isSubmersionOfComplement_complement V U hVU).isSubmersion

theorem IsActualTowerPullback.exists_actual_masked_companion (hn : 0 < n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (o : ℕ) :
    ∃ p : ordMask (geoTransformAlong (markedPullback (m := m) f M) Q) o →
        ordMask (geoTransformAlong M T) o,
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ p ∧
      (∀ z, (p z : D) = g (z : D')) ∧
      markedPullback (m := m) p (compAt M o T) = compAt (markedPullback (m := m) f M) o Q := by
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) Q) o
  let U := ordMask (geoTransformAlong M T) o
  have hVU : MapsTo g V U := by
    intro z hz
    have he := IsActualTowerPullback.order_mask_dictionary hn h M hM hT o
    change z ∈ (ordMask (geoTransformAlong (markedPullback (m := m) f M) Q) o : Set D') at hz
    rw [he] at hz
    exact hz
  let p : V → U := restrictedOpenMap V U hVU
  have hp := restrictedOpenMap_isSubmersion h.isSubmersion V U hVU
  have hc := isInvDomain_geoTransformAlong hM T hT
  have hcu := isInvDomain_pullback_val U hc
  have he : markedPullback (m := m) p
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → D) (geoTransformAlong M T)) =
      MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : V → D')
        (geoTransformAlong (markedPullback (m := m) f M) Q) := by
    rw [(IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hT).2]
    change markedPullback (m := m) p
        (markedPullback (m := n) (Subtype.val : U → D) (geoTransformAlong M T)) =
      markedPullback (m := m) (Subtype.val : V → D')
        (markedPullback (m := m) g (geoTransformAlong M T))
    rw [← whole_parameter_markedPullback_comp (X := D) (Y := CMfd.of (n := n) U) (Z := CMfd.of (n := m) V) (f := (Subtype.val : U → D)) (g := p) contMDiff_subtype_val hp.contMDiff _ hc.isWellFormed.isCoherent,
      ← whole_parameter_markedPullback_comp (X := D) (Y := D') (Z := CMfd.of (n := m) V) (f := g) (g := (Subtype.val : V → D')) h.isSubmersion.contMDiff contMDiff_subtype_val _ hc.isWellFormed.isCoherent]
    rfl
  refine ⟨p,hp,fun _ => rfl,?_⟩
  change markedPullback (m := m) p
      (companionOf n (M := CMfd.of (n := n) U) (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → D) (geoTransformAlong M T)) o) =
    companionOf m (M := CMfd.of (n := m) V) (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : V → D')
      (geoTransformAlong (markedPullback (m := m) f M) Q)) o
  rw [markedPullback_companionOf (X := CMfd.of (n := n) U) (Y := CMfd.of (n := m) V) (f := p) hp hn _ hcu.isWellFormed hcu.isNonzeroAlongAt o,he]

theorem IsActualTowerPullback.exists_split_historical_masked_companion (hn : 0 < n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (j o : ℕ) :
    ∃ a : (split Q j).1 → (split T j).1,
      IsActualTowerPullback f (head Q j) (head T j) a ∧
      IsActualTowerPullback a (tail Q j) (tail T j) g ∧
      ∃ p : ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q j)) o →
          ordMask (geoTransformAlong M (head T j)) o,
        Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ p ∧
        (∀ z, (p z : (split T j).1) = a (z : (split Q j).1)) ∧
        markedPullback (m := m) p (compAt M o (head T j)) =
          compAt (markedPullback (m := m) f M) o (head Q j) := by
  obtain ⟨a,ha,htail⟩ := IsActualTowerPullback.simultaneous_split h j
  have hh := ((isGeoTestTower_iff_head_tail M T j).mp hT).1
  exact ⟨a,ha,htail,IsActualTowerPullback.exists_actual_masked_companion hn ha M hM hh o⟩

theorem IsActualTowerPullback.exists_own_companionAt_dictionary (hn : 0 < n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (z : D') :
    ∃ p : maskAt (markedPullback (m := m) f M) Q z → maskAt M T (g z),
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ p ∧
      markedPullback (m := m) p (companionAt M T (g z)) =
        companionAt (markedPullback (m := m) f M) Q z := by
  have ho := IsActualTowerPullback.orderAt_dictionary hn h M hM hT z
  have hr := IsActualTowerPullback.runAt_dictionary hn h M hM hT z
  unfold companionAt maskAt
  rw [hr,ho]
  obtain ⟨a,_,_,p,hp,_,he⟩ := IsActualTowerPullback.exists_split_historical_masked_companion
    hn h M hM hT (runAt M T (g z)) (orderAt M T (g z))
  exact ⟨p,hp,he⟩

theorem IsActualTowerPullback.whole_patchAt_dictionary (hn : 0 < n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (z : D') :
    (patchAt (markedPullback (m := m) f M) Q z : Set D') =
      g ⁻¹' (patchAt M T (g z) : Set D) := by
  have ho := IsActualTowerPullback.orderAt_dictionary hn h M hM hT z
  have hr := IsActualTowerPullback.runAt_dictionary hn h M hM hT z
  unfold patchAt maskAt
  rw [hr,ho]
  let j := runAt M T (g z)
  obtain ⟨a,hhead,htail⟩ := IsActualTowerPullback.simultaneous_split h j
  have hh := ((isGeoTestTower_iff_head_tail M T j).mp hT).1
  have hm := IsActualTowerPullback.order_mask_dictionary hn hhead M hM hh (orderAt M T (g z))
  ext w
  change (tail Q j).proj w ∈ (ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q j))
    (orderAt M T (g z)) : Set (split Q j).1) ↔
    (tail T j).proj (g w) ∈ (ordMask (geoTransformAlong M (head T j))
      (orderAt M T (g z)) : Set (split T j).1)
  rw [hm]
  have hs : (tail T j).proj (g w) = a ((tail Q j).proj w) := htail.proj_comm w
  change a ((tail Q j).proj w) ∈ (ordMask (geoTransformAlong M (head T j))
    (orderAt M T (g z)) : Set (split T j).1) ↔
    (tail T j).proj (g w) ∈ (ordMask (geoTransformAlong M (head T j))
      (orderAt M T (g z)) : Set (split T j).1)
  rw [← hs]

private def HistoricalMaskModel (M : MarkedIdeal n X)
    (Q : BlowupTower Y D') (T : BlowupTower X D) (g : D' → D) : Prop :=
  ∀ z : D',
    (patchAt (markedPullback (m := m) f M) Q z : Set D') = g ⁻¹' (patchAt M T (g z) : Set D) ∧
    ∃ p : maskAt (markedPullback (m := m) f M) Q z → maskAt M T (g z),
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ p ∧
      markedPullback (m := m) p (companionAt M T (g z)) =
        companionAt (markedPullback (m := m) f M) Q z

theorem exists_original_only_historical_companion_masks (hn : 0 < n)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g ∧
      Q.length = T.length ∧
      HironakaSmoothSubmersionOrderedChoiceBaseChange.HolomorphicSquarePullback f g Q.proj T.proj ∧
      HistoricalMaskModel (f := f) M Q T g := by
  obtain ⟨D',Q,g,h⟩ := exists_actual_tower hf T
  refine ⟨D',Q,g,h,h.isSubmersion,h.length_eq,h.universal,?_⟩
  intro z
  exact ⟨IsActualTowerPullback.whole_patchAt_dictionary hn h M hM hT z,
    IsActualTowerPullback.exists_own_companionAt_dictionary hn h M hM hT z⟩

end
end Hironaka.HironakaSmoothSubmersionHistoricalCompanionMasks
