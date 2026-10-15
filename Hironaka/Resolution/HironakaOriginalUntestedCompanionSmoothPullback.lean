/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalUntestedSpecialSmoothPullback
import Hironaka.Resolution.HironakaSmoothSubmersionHistoricalCompanionMasks
/-! Actual order-run masks and independently computed whole companions from
genuine current domains on upper TESTs, without a candidate TEST. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalUntestedCompanionSmoothPullback
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionRelativePartsCompanion
  HironakaSmoothSubmersionHistoricalCompanionMasks HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionBlowupLift HironakaSmoothSubmersionContactParameterCoefficientIdeals
  HironakaOriginalUntestedControlledSmoothPullback HironakaStepOneMemberLowerExtension
  HironakaStepOneMemberTailExtension InvDomainMemberRestriction InvDomainTowerAlong
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail CompanionRebase
  StepOneRegime MarkedIdealBiholomorphism GeneralValue
  HironakaSmoothSubmersionContactParameterCharts HironakaGeneralThreeNonspecialAnalyticLoci
open ResolutionInvariantSpec (IsInvDomain)
variable {n m b : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

/-- True whole controlled records and independently proved current domain
supply original order equality without candidate admissibility. -/
theorem IsActualTowerPullback.modeled_orderAt_dictionary (hn : 0<n)
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      IsInvDomain b (geoTransformAlong K R)) (hT : IsGeoTestTower M T) (z : D') :
    orderAt (markedPullback (m := m) f K) Q z=orderAt K T (g z) := by
  have hWhole := (IsActualTowerPullback.modeled_controlled_dictionary h M K
    (fun R hR => (hModel R hR).isWellFormed) hT).1
  unfold orderAt
  rw [hWhole]
  exact nmOrd_markedPullback h.isSubmersion hn _ (hModel T hT).isWellFormed
    (hModel T hT).isNonzeroAlongAt z

/-- Both actual current cosupport and true original order are transported
before comparing the unchanged original fixed-order regime. -/
theorem IsActualTowerPullback.modeled_ordRegime_dictionary (hn : 0<n)
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      IsInvDomain b (geoTransformAlong K R)) (hT : IsGeoTestTower M T) (q : ℕ) (z : D') :
    OrdRegime (markedPullback (m := m) f K) q Q z ↔ OrdRegime K q T (g z) := by
  change (z ∈ (geoTransformAlong (markedPullback (m := m) f K) Q).cosupp ∧
      orderAt (markedPullback (m := m) f K) Q z=q) ↔
    (g z ∈ (geoTransformAlong K T).cosupp ∧ orderAt K T (g z)=q)
  rw [(IsActualTowerPullback.modeled_controlled_dictionary h M K
    (fun R hR => (hModel R hR).isWellFormed) hT).2,
    IsActualTowerPullback.modeled_orderAt_dictionary hn h M K hModel hT z]
  rfl

/-- Every true reset/increment equation is retained on the literal actual
Cartesian histories, with no candidate TEST or supplied run. -/
theorem IsActualTowerPullback.modeled_fixed_order_run (hn : 0<n)
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      IsInvDomain b (geoTransformAlong K R)) (hT : IsGeoTestTower M T) (q : ℕ) :
    ∀ z : D',regimeRun (OrdRegime (markedPullback (m := m) f K) q) Q z=
      regimeRun (OrdRegime K q) T (g z) := by
  induction h with
  | refl => intro z;rfl
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    intro z
    have hp := IsActualTowerPullback.modeled_ordRegime_dictionary hn h M K hModel hT.1 q (ρ z)
    have hSquare : π (actualLift hg hπ hρ z)=g (ρ z) := congrFun (actualLift_proj_comm hg hπ hρ) z
    rw [regimeRun_step,regimeRun_step,hSquare]
    by_cases hz : OrdRegime K q T (g (ρ z))
    · rw [if_pos (hp.mpr hz),if_pos hz,ih hT.1]
    · rw [if_neg (fun hh => hz (hp.mp hh)),if_neg hz]

/-- The actual source order open is the entire inverse image of the target
open, from genuine coherent nonmonomial-part geometry. -/
theorem IsActualTowerPullback.modeled_order_mask_dictionary (hn : 0<n)
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      IsInvDomain b (geoTransformAlong K R)) (hT : IsGeoTestTower M T) (q : ℕ) :
    (ordMask (geoTransformAlong (markedPullback (m := m) f K) Q) q : Set D')=
      g ⁻¹' (ordMask (geoTransformAlong K T) q : Set D) := by
  rw [(IsActualTowerPullback.modeled_controlled_dictionary h M K
    (fun R hR => (hModel R hR).isWellFormed) hT).1]
  exact ordMask_markedPullback h.isSubmersion hn _ (hModel T hT).isWellFormed
    (hModel T hT).isNonzeroAlongAt q

/-- True independently computed order masks and real coherent pullback
composition precede the ALL FOUR fields of both actual compAt records. -/
theorem IsActualTowerPullback.exists_modeled_masked_companion (hn : 0<n)
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      IsInvDomain b (geoTransformAlong K R)) (hT : IsGeoTestTower M T) (q : ℕ) :
    ∃ p : ordMask (geoTransformAlong (markedPullback (m := m) f K) Q) q →
        ordMask (geoTransformAlong K T) q,
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ p ∧
      (∀ z,(p z : D)=g (z : D')) ∧
      markedPullback (m := m) p (compAt K q T)=compAt (markedPullback (m := m) f K) q Q := by
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f K) Q) q
  let U := ordMask (geoTransformAlong K T) q
  have hVU : MapsTo g V U := by
    intro z hz
    change z ∈ (V : Set D') at hz
    rw [IsActualTowerPullback.modeled_order_mask_dictionary hn h M K hModel hT q] at hz
    exact hz
  let p : V → U := restrictedOpenMap V U hVU
  have hp := restrictedOpenMap_isSubmersion h.isSubmersion V U hVU
  have hc := hModel T hT
  have hcu := isInvDomain_pullback_val U hc
  have hWhole := (IsActualTowerPullback.modeled_controlled_dictionary h M K
    (fun R hR => (hModel R hR).isWellFormed) hT).1
  have he : markedPullback (m := m) p
      (MarkedIdeal.pullback (Subtype.val : U → D) (geoTransformAlong K T))=
      MarkedIdeal.pullback (Subtype.val : V → D')
        (geoTransformAlong (markedPullback (m := m) f K) Q) := by
    rw [hWhole]
    change markedPullback (m := m) p
        (markedPullback (m := n) (Subtype.val : U → D) (geoTransformAlong K T))=
      markedPullback (m := m) (Subtype.val : V → D')
        (markedPullback (m := m) g (geoTransformAlong K T))
    rw [←whole_parameter_markedPullback_comp (X := D) (Y := CMfd.of (n := n) U)
        (Z := CMfd.of (n := m) V) (f := (Subtype.val : U → D)) (g := p)
        contMDiff_subtype_val hp.contMDiff _ hc.isWellFormed.isCoherent,
      ←whole_parameter_markedPullback_comp (X := D) (Y := D') (Z := CMfd.of (n := m) V)
        (f := g) (g := (Subtype.val : V → D')) h.isSubmersion.contMDiff
        contMDiff_subtype_val _ hc.isWellFormed.isCoherent]
    rfl
  refine ⟨p,hp,fun _ => rfl,?_⟩
  change markedPullback (m := m) p
      (companionOf n (M := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → D) (geoTransformAlong K T)) q)=
    companionOf m (M := CMfd.of (n := m) V) (MarkedIdeal.pullback (Subtype.val : V → D')
      (geoTransformAlong (markedPullback (m := m) f K) Q)) q
  rw [markedPullback_companionOf (X := CMfd.of (n := n) U) (Y := CMfd.of (n := m) V)
    (f := p) hp hn _ hcu.isWellFormed hcu.isNonzeroAlongAt q,he]

/-- The same real split map simultaneously serves the actual upper head and
tail before constructing the independent actual companion masks. -/
theorem IsActualTowerPullback.exists_modeled_split_masked_companion (hn : 0<n)
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      IsInvDomain b (geoTransformAlong K R)) (hT : IsGeoTestTower M T) (j q : ℕ) :
    ∃ a : (split Q j).1 → (split T j).1,
      IsActualTowerPullback f (head Q j) (head T j) a ∧
      IsActualTowerPullback a (tail Q j) (tail T j) g ∧
      ∃ p : ordMask (geoTransformAlong (markedPullback (m := m) f K) (head Q j)) q →
          ordMask (geoTransformAlong K (head T j)) q,
        Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ p ∧
        (∀ z,(p z : (split T j).1)=a (z : (split Q j).1)) ∧
        markedPullback (m := m) p (compAt K q (head T j))=
          compAt (markedPullback (m := m) f K) q (head Q j) := by
  obtain ⟨a,hHead,hTail⟩ := HironakaSmoothSubmersionHistoricalCompanionMasks.IsActualTowerPullback.simultaneous_split h j
  have hTJ := ((isGeoTestTower_iff_head_tail M T j).mp hT).1
  exact ⟨a,hHead,hTail,IsActualTowerPullback.exists_modeled_masked_companion hn hHead M K hModel hTJ q⟩

/-- ONLY original member geometry supplies every real candidate-domain
premise before the actual original order-run and companion diagram. -/
theorem original_member_untested_order_companion_history (hn : 0<n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain b M)
    (S : Finset (Fin M.E.length)) (hS : S.Nonempty) (hT : IsGeoTestTower M T) :
    let K := memberRemainderMarked M S
    (∀ q : ℕ,∀ z : D',regimeRun (OrdRegime (markedPullback (m := m) f K) q) Q z=
      regimeRun (OrdRegime K q) T (g z)) ∧
    ∀ j q : ℕ,∃ a : (split Q j).1 → (split T j).1,
      IsActualTowerPullback f (head Q j) (head T j) a ∧
      IsActualTowerPullback a (tail Q j) (tail T j) g ∧
      ∃ p : ordMask (geoTransformAlong (markedPullback (m := m) f K) (head Q j)) q →
          ordMask (geoTransformAlong K (head T j)) q,
        Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ p ∧
        (∀ z,(p z : (split T j).1)=a (z : (split Q j).1)) ∧
        markedPullback (m := m) p (compAt K q (head T j))=
          compAt (markedPullback (m := m) f K) q (head Q j) := by
  let K := memberRemainderMarked M S
  have hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      IsInvDomain (b-1) (geoTransformAlong K R) := fun R hR =>
    isInvDomain_geoTransformAlong_memberRemainder hn M hM.isWellFormed hM.one_le_d hM.dimLE S hS R hR
  exact ⟨fun q => IsActualTowerPullback.modeled_fixed_order_run hn h M K hModel hT q,
    fun j q => IsActualTowerPullback.exists_modeled_split_masked_companion hn h M K hModel hT j q⟩

end
end Hironaka.HironakaOriginalUntestedCompanionSmoothPullback
