/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalUntestedControlledSmoothPullback
/-! Actual candidate SPECIAL/level/run smooth naturality from independently
proved controlled geometry, without a candidate TEST. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalUntestedSpecialSmoothPullback
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneRegime StepOneLowerDomain
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionPositiveMemberHistory HironakaSmoothSubmersionAllBranchHistory
  HironakaSmoothSubmersionRelativeOrder HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionBlowupLift HironakaOriginalUntestedControlledSmoothPullback
  HironakaOriginalUntestedMemberCurveSpecial HironakaStepOneMemberLowerExtension
  HironakaStepOneMemberTailExtension MemberInterLocusAlong CodimOneSupportAlong
  InvDomainMemberRestriction HironakaCoherentTransformExtension NormalCrossings
  MarkedIdealOperationsAlong
open ResolutionInvariantSpec (IsInvDomain)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

private theorem actual_base_submersion (h : IsActualTowerPullback f Q T g) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f := by
  induction h with
  | refl hf => exact hf
  | step _ _ _ _ ih => exact ih

/-- Real bar geometry supplies whole controlled naturality on the SAME upper
TEST without making either candidate history a TEST. -/
theorem IsActualTowerPullback.modeled_bar_dictionary
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X) (hK : K.IsWellFormed)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      (geoTransformAlong (barMarked K) R).IsWellFormed) (hT : IsGeoTestTower M T) :
    geoTransformAlong (barMarked (markedPullback (m := m) f K)) Q=
      markedPullback (m := m) g (geoTransformAlong (barMarked K) T) := by
  have hh := (IsActualTowerPullback.modeled_controlled_dictionary h M (barMarked K) hModel hT).1
  rwa [pullback_barMarked (actual_base_submersion h) K hK] at hh

/-- Taking the literal original-boundary prefix commutes with the actual
smooth preimage; every indexed empty or repeated position remains. -/
theorem IsActualTowerPullback.modeled_original_members_dictionary
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X) (hK : K.IsWellFormed)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      (geoTransformAlong (barMarked K) R).IsWellFormed) (hT : IsGeoTestTower M T) :
    origMembers (markedPullback (m := m) f K) Q=(origMembers K T).map (g ⁻¹' ·) := by
  unfold origMembers
  rw [IsActualTowerPullback.modeled_bar_dictionary h M K hK hModel hT]
  simp only [markedPullback,List.length_map,List.map_take]

/-- Actual indexed level equality does not require a candidate TEST. -/
theorem IsActualTowerPullback.modeled_level_dictionary
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X) (hK : K.IsWellFormed)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      (geoTransformAlong (barMarked K) R).IsWellFormed) (hT : IsGeoTestTower M T) (z : D') :
    level (markedPullback (m := m) f K) Q z=level K T (g z) := by
  unfold level
  rw [IsActualTowerPullback.modeled_original_members_dictionary h M K hK hModel hT]
  exact CodimOnePartCanonical.boundaryCount_map_preimage g _ z

private theorem modeled_member_locus_dictionary
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X) (hK : K.IsWellFormed)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      (geoTransformAlong (barMarked K) R).IsWellFormed) (hT : IsGeoTestTower M T) :
    memberInterLocus (geoTransformAlong (barMarked (markedPullback (m := m) f K)) Q).N
      (origMembers (markedPullback (m := m) f K) Q)
      (geoTransformAlong (barMarked (markedPullback (m := m) f K)) Q).cosupp=
    g ⁻¹' memberInterLocus (geoTransformAlong (barMarked K) T).N (origMembers K T)
      (geoTransformAlong (barMarked K) T).cosupp := by
  rw [IsActualTowerPullback.modeled_bar_dictionary h M K hK hModel hT,
    IsActualTowerPullback.modeled_original_members_dictionary h M K hK hModel hT]
  change memberInterLocus (g ⁻¹' (geoTransformAlong (barMarked K) T).N)
    ((origMembers K T).map (g ⁻¹' ·))
    (GermIdealOrder.cosupport m (g ⁻¹' (geoTransformAlong (barMarked K) T).N)
      (GermIdeal.pullback (m := m) g (geoTransformAlong (barMarked K) T).ideal)
      (geoTransformAlong (barMarked K) T).d)=_
  rw [cosupport_preimage_eq h.isSubmersion (hModel T hT).isCoherent]
  exact memberInterLocus_preimage g
    (fun z => HironakaSmoothSubmersionDivisorExponents.map_nhds_submersion_eq
      (h.isSubmersion.isSubmersionAt z)) _ _ _

/-- Genuine codimension-one and member-locus geometry reflects BOTH actual
SPECIAL branches of an untested candidate. -/
theorem IsActualTowerPullback.modeled_isSpecial_dictionary
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X) (hK : K.IsWellFormed)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      (geoTransformAlong (barMarked K) R).IsWellFormed) (hT : IsGeoTestTower M T) (z : D') :
    IsSpecial (markedPullback (m := m) f K) Q z ↔ IsSpecial K T (g z) := by
  have hCodim : codimOnePartAlong
      (geoTransformAlong (barMarked (markedPullback (m := m) f K)) Q).N
      (geoTransformAlong (barMarked (markedPullback (m := m) f K)) Q).ideal
      (geoTransformAlong (barMarked (markedPullback (m := m) f K)) Q).d=
      g ⁻¹' codimOnePartAlong (geoTransformAlong (barMarked K) T).N
        (geoTransformAlong (barMarked K) T).ideal (geoTransformAlong (barMarked K) T).d := by
    rw [IsActualTowerPullback.modeled_bar_dictionary h M K hK hModel hT]
    exact codimOnePartAlong_preimage_eq h.isSubmersion (hModel T hT).isCoherent _ _
  unfold IsSpecial
  rw [IsActualTowerPullback.modeled_level_dictionary h M K hK hModel hT z,
    hCodim,modeled_member_locus_dictionary h M K hK hModel hT]
  rfl

/-- The actual nonspecial regime is compared only after its true two-sided
geometric SPECIAL and indexed-level dictionaries. -/
theorem IsActualTowerPullback.modeled_stepRegime_dictionary
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X) (hK : K.IsWellFormed)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      (geoTransformAlong (barMarked K) R).IsWellFormed) (hT : IsGeoTestTower M T) (s : ℕ) (z : D') :
    stepRegime (markedPullback (m := m) f K) s Q z ↔ stepRegime K s T (g z) := by
  change (_=s ∧ ¬ IsSpecial _ Q z) ↔ (_=s ∧ ¬ IsSpecial K T (g z))
  rw [IsActualTowerPullback.modeled_level_dictionary h M K hK hModel hT z,
    IsActualTowerPullback.modeled_isSpecial_dictionary h M K hK hModel hT z]

/-- The literal original reset/increment recursion remains natural for every
modeled candidate, including every empty blowup position. -/
theorem IsActualTowerPullback.modeled_stepRegime_run
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X) (hK : K.IsWellFormed)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      (geoTransformAlong (barMarked K) R).IsWellFormed) (hT : IsGeoTestTower M T) (s : ℕ) :
    ∀ z : D',regimeRun (stepRegime (markedPullback (m := m) f K) s) Q z=
      regimeRun (stepRegime K s) T (g z) := by
  induction h with
  | refl => intro z;rfl
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    intro z
    have hp := IsActualTowerPullback.modeled_stepRegime_dictionary h M K hK hModel hT.1 s (ρ z)
    have hSquare : π (actualLift hg hπ hρ z)=g (ρ z) := congrFun (actualLift_proj_comm hg hπ hρ) z
    rw [regimeRun_step,regimeRun_step,hSquare]
    by_cases hz : stepRegime K s T (g (ρ z))
    · rw [if_pos (hp.mpr hz),if_pos hz,ih hT.1]
    · rw [if_neg (fun hh => hz (hp.mp hh)),if_neg hz]

private theorem modeled_same_geometry_wellFormed (M K B : MarkedIdeal n X)
    (hB : B.IsWellFormed) (hN : B.N=K.N) (hE : B.E=K.E)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      (geoTransformAlong K R).IsWellFormed) :
    ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      (geoTransformAlong B R).IsWellFormed
  | _,.refl,_ => hB
  | _,.step R C π hπ,hR => by
    have hPrev := modeled_same_geometry_wellFormed M K B hB hN hE hModel R hR.1
    have hNext := hModel (.step R C π hπ) hR
    have hN' := geoTransformAlong_N_eq_of_N_eq hN (.step R C π hπ)
    have hE' := geoTransformAlong_E_eq_of_E_eq hE (.step R C π hπ)
    have hSM : IsClosedSubmanifold n ((geoTransformAlong B R).geoTransform C π).N := by
      change IsClosedSubmanifold n (geoTransformAlong B (.step R C π hπ)).N
      rw [hN'];exact hNext.isClosedSubmanifold_N
    refine ⟨hSM,isCoherent_geoTransform_ideal_of_smooth_strict _ hPrev.isCoherent hπ hSM,?_,?_⟩
    · rw [hE'];exact hNext.isSNCDivisor
    · rw [hN',hE'];exact hNext.isTransverse

/-- ONLY original member DOMAIN b/ANY upper TEST internally supply genuine
candidate bar geometry before ALL heads' SPECIAL and actual run comparisons. -/
theorem original_member_untested_special_all_heads (hn : 0<n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) {b : ℕ} (hM : IsInvDomain b M)
    (S : Finset (Fin M.E.length)) (hS : S.Nonempty) (hT : IsGeoTestTower M T) :
    let K := memberRemainderMarked M S
    (∀ s : ℕ,∀ z : D',regimeRun (stepRegime (markedPullback (m := m) f K) s) Q z=
      regimeRun (stepRegime K s) T (g z)) ∧
    ∀ j : ℕ,∃ a : (split Q j).1 → (split T j).1,
      IsActualTowerPullback f (head Q j) (head T j) a ∧
      geoTransformAlong (barMarked (markedPullback (m := m) f K)) (head Q j)=
        markedPullback (m := m) a (geoTransformAlong (barMarked K) (head T j)) ∧
      ∀ z : (split Q j).1,
        level (markedPullback (m := m) f K) (head Q j) z=level K (head T j) (a z) ∧
        (IsSpecial (markedPullback (m := m) f K) (head Q j) z ↔ IsSpecial K (head T j) (a z)) := by
  let K := memberRemainderMarked M S
  have hK : IsInvDomain (b-1) K := isInvDomain_memberRemainderMarked hn M hM.isWellFormed
    hM.one_le_d hM.dimLE S hS
  have hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      (geoTransformAlong (barMarked K) R).IsWellFormed := by
    intro V R hR
    exact modeled_same_geometry_wellFormed M K (barMarked K)
      (isWellFormed_barMarked K hK.isWellFormed) rfl rfl
      (fun R hR => (isInvDomain_geoTransformAlong_memberRemainder hn M hM.isWellFormed
        hM.one_le_d hM.dimLE S hS R hR).isWellFormed) R hR
  refine ⟨fun s => IsActualTowerPullback.modeled_stepRegime_run h M K hK.isWellFormed hModel hT s,fun j => ?_⟩
  obtain ⟨a,ha⟩ := h.head j
  have hTJ := ((isGeoTestTower_iff_head_tail M T j).mp hT).1
  exact ⟨a,ha,IsActualTowerPullback.modeled_bar_dictionary ha M K hK.isWellFormed hModel hTJ,
    fun z => ⟨IsActualTowerPullback.modeled_level_dictionary ha M K hK.isWellFormed hModel hTJ z,
      IsActualTowerPullback.modeled_isSpecial_dictionary ha M K hK.isWellFormed hModel hTJ z⟩⟩

end
end Hironaka.HironakaOriginalUntestedSpecialSmoothPullback
