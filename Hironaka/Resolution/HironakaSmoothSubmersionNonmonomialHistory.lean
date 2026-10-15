/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionRelativePartsCompanion
import Hironaka.Resolution.HironakaGeneralThreeNonspecialAnalyticLoci
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionNonmonomialHistory
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec InvDomainTowerAlong
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionRelativePartsCompanion HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeOrder HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionBlowupLift StepOneValue StepOneRegime NonmonomialOrderRegime
  NonmonomialOrderLocal HironakaGeneralThreeNonspecialAnalyticLoci CompanionRebase
noncomputable section
variable {n m k : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

theorem origMembers_eq_current_boundary (M : MarkedIdeal n X) (T : BlowupTower X D) :
    origMembers M T = (geoTransformAlong M T).E.take M.E.length := by
  rw [origMembers_eq,MemberInterTowerAlong.take_E_geoTransformAlong]

theorem IsActualTowerPullback.original_members_dictionary
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower M T) :
    origMembers (markedPullback (m := m) f M) Q =
      (origMembers M T).map (g ⁻¹' ·) := by
  have hmark := (IsActualTowerPullback.relative_marked_dictionary h M hM hT).2
  have hE := congrArg MarkedIdeal.E hmark
  rw [origMembers_eq_current_boundary,origMembers_eq_current_boundary,hE]
  simp only [markedPullback,List.length_map,List.map_take]

theorem IsActualTowerPullback.level_dictionary
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower M T) (z : D') :
    level (markedPullback (m := m) f M) Q z = level M T (g z) := by
  unfold level
  rw [IsActualTowerPullback.original_members_dictionary h M hM hT]
  exact CodimOnePartCanonical.boundaryCount_map_preimage g _ z

theorem IsActualTowerPullback.orderAt_dictionary (hn : 0 < n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (z : D') :
    orderAt (markedPullback (m := m) f M) Q z = orderAt M T (g z) := by
  have hcurrent := isInvDomain_geoTransformAlong hM T hT
  unfold orderAt
  rw [(IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hT).2]
  exact nmOrd_markedPullback h.isSubmersion hn _ hcurrent.isWellFormed
    hcurrent.isNonzeroAlongAt z

theorem IsActualTowerPullback.ordRegime_dictionary (hn : 0 < n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (o : ℕ) (z : D') :
    OrdRegime (markedPullback (m := m) f M) o Q z ↔ OrdRegime M o T (g z) := by
  change (z ∈ (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp ∧
      orderAt (markedPullback (m := m) f M) Q z = o) ↔
    (g z ∈ (geoTransformAlong M T).cosupp ∧ orderAt M T (g z) = o)
  rw [IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed hT,
    IsActualTowerPullback.orderAt_dictionary hn h M hM hT]
  rfl

theorem IsActualTowerPullback.fixed_order_regime_run (hn : 0 < n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (o : ℕ) :
    ∀ z : D', regimeRun (OrdRegime (markedPullback (m := m) f M) o) Q z =
      regimeRun (OrdRegime M o) T (g z) := by
  classical
  induction h with
  | refl => intro z; rfl
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    intro z
    obtain ⟨hTT,_⟩ := hT
    have hp := IsActualTowerPullback.ordRegime_dictionary hn h M hM hTT o (ρ z)
    have hsquare : π (actualLift hg hπ hρ z) = g (ρ z) :=
      congrFun (actualLift_proj_comm hg hπ hρ) z
    rw [regimeRun_step,regimeRun_step,hsquare]
    by_cases hz : OrdRegime M o T (g (ρ z))
    · rw [if_pos (hp.mpr hz),if_pos hz,ih hTT]
    · rw [if_neg (fun hh => hz (hp.mp hh)),if_neg hz]

theorem IsActualTowerPullback.runAt_dictionary (hn : 0 < n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (z : D') :
    runAt (markedPullback (m := m) f M) Q z = runAt M T (g z) := by
  unfold runAt
  rw [IsActualTowerPullback.orderAt_dictionary hn h M hM hT]
  exact IsActualTowerPullback.fixed_order_regime_run hn h M hM hT _ z

theorem IsActualTowerPullback.fresh_companion_dictionary (hn : 0 < n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (o : ℕ) :
    markedPullback (m := m) g (companionOf n (geoTransformAlong M T) o) =
      companionOf m (geoTransformAlong (markedPullback (m := m) f M) Q) o := by
  have hcurrent := isInvDomain_geoTransformAlong hM T hT
  rw [(IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hT).2]
  exact markedPullback_companionOf h.isSubmersion hn _ hcurrent.isWellFormed
    hcurrent.isNonzeroAlongAt o

private def StageHistory (M : MarkedIdeal n X) (Q : BlowupTower Y D')
    (T : BlowupTower X D) (g : D' → D) : Prop :=
  IsGeoTestTower (markedPullback (m := m) f M) Q ∧
  geoTransformAlong (markedPullback (m := m) f M) Q =
    markedPullback (m := m) g (geoTransformAlong M T) ∧
  origMembers (markedPullback (m := m) f M) Q = (origMembers M T).map (g ⁻¹' ·) ∧
  (∀ z : D', level (markedPullback (m := m) f M) Q z = level M T (g z) ∧
    orderAt (markedPullback (m := m) f M) Q z = orderAt M T (g z) ∧
    runAt (markedPullback (m := m) f M) Q z = runAt M T (g z)) ∧
  (∀ o : ℕ, ∀ z : D', regimeRun (OrdRegime (markedPullback (m := m) f M) o) Q z =
    regimeRun (OrdRegime M o) T (g z)) ∧
  (∀ o : ℕ, markedPullback (m := m) g (companionOf n (geoTransformAlong M T) o) =
    companionOf m (geoTransformAlong (markedPullback (m := m) f M) Q) o)

theorem IsActualTowerPullback.stage_history (hn : 0 < n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) : StageHistory (f := f) M Q T g := by
  obtain ⟨hQ,hmark⟩ := IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hT
  exact ⟨hQ,hmark,IsActualTowerPullback.original_members_dictionary h M hM.isWellFormed hT,
    fun z => ⟨IsActualTowerPullback.level_dictionary h M hM.isWellFormed hT z,
      IsActualTowerPullback.orderAt_dictionary hn h M hM hT z,
      IsActualTowerPullback.runAt_dictionary hn h M hM hT z⟩,
    fun o => IsActualTowerPullback.fixed_order_regime_run hn h M hM hT o,
    fun o => IsActualTowerPullback.fresh_companion_dictionary hn h M hM hT o⟩

theorem IsActualTowerPullback.all_literal_head_histories (hn : 0 < n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (j : ℕ) :
    ∃ a : (split Q j).1 → (split T j).1,
      IsActualTowerPullback f (head Q j) (head T j) a ∧
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ a ∧
      StageHistory (f := f) M (head Q j) (head T j) a := by
  obtain ⟨a,ha⟩ := h.head j
  have hTH := ((isGeoTestTower_iff_head_tail M T j).mp hT).1
  exact ⟨a,ha,ha.isSubmersion,IsActualTowerPullback.stage_history hn ha M hM hTH⟩

theorem exists_original_only_entire_nonmonomial_history (hn : 0 < n)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g ∧
      Q.length = T.length ∧
      HironakaSmoothSubmersionOrderedChoiceBaseChange.HolomorphicSquarePullback f g Q.proj T.proj ∧
      StageHistory (f := f) M Q T g ∧
      ∀ j : ℕ, ∃ a : (split Q j).1 → (split T j).1,
        IsActualTowerPullback f (head Q j) (head T j) a ∧
        Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ a ∧
        StageHistory (f := f) M (head Q j) (head T j) a := by
  obtain ⟨D',Q,g,h⟩ := exists_actual_tower hf T
  exact ⟨D',Q,g,h,h.isSubmersion,h.length_eq,h.universal,
    IsActualTowerPullback.stage_history hn h M hM hT,
    fun j => IsActualTowerPullback.all_literal_head_histories hn h M hM hT j⟩

end
end Hironaka.HironakaSmoothSubmersionNonmonomialHistory
