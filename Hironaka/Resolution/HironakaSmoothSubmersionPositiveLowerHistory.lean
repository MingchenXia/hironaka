/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionAllBranchHistory
import Hironaka.Invariant.MemberRestrictTowerIso
/-! # Actual original positive Step One lower records and selected histories

Smooth SNC germ separation supplies through-point original-member reflection
without global preimage injectivity. The entire actual coefficient restriction,
whole positive masked lower record, actual split maps and whole restricted
Cartesian tails are produced from the original datum and actual test history.
Chosen zero-contact comparison and ambient-dependent higher invariant values
remain further producers. Mathematics was written before these proofs.
Blueprint: `hironaka-smooth-submersion-positive-lower-history-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionPositiveLowerHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  BlowupTowerSplit StepOneValue StepOneValueMasked StepOneLowerDomain
  InvDomainMemberRestriction InvDomainRebase HomogenizedIdealAlong CoefficientIdealRestriction
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionNormalCrossings
  HironakaSmoothSubmersionRelativeDifferentialIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionPositiveMemberHistory HironakaSmoothSubmersionAllBranchHistory
  HironakaSmoothSubmersionHistoricalCompanionMasks HironakaSmoothSubmersionHistoricalControlledTail
  HironakaSmoothSubmersionContactParameterCharts HironakaSmoothSubmersionContactParameterCoefficientIdeals

variable {n m : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}

/-- Smooth SNC germ separation reflects original-member membership only
for actual members through the selected point. Empty entries are retained. -/
theorem mem_of_preimage_mem_map_through
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {E E₀ : List (Set X)} (hE : NormalCrossings.IsSNCDivisor n E)
    (hE₀ : ∀ H ∈ E₀, H ∈ E) {H : Set X} (hH : H ∈ E) {z : Y}
    (hz : f z ∈ H) (h : f ⁻¹' H ∈ E₀.map (f ⁻¹' ·)) : H ∈ E₀ := by
  obtain ⟨H₀,hH₀,hpre⟩ := List.mem_map.mp h
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (hE₀ H₀ hH₀)
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hH
  let i' : Fin (E.map (f ⁻¹' ·)).length := ⟨i.val,by simp⟩
  let j' : Fin (E.map (f ⁻¹' ·)).length := ⟨j.val,by simp⟩
  have hi' : (E.map (f ⁻¹' ·)).get i' = f ⁻¹' H₀ := by
    simpa [i'] using congrArg (fun W => f ⁻¹' W) hi
  have hj' : (E.map (f ⁻¹' ·)).get j' = f ⁻¹' H := by
    simpa [j'] using congrArg (fun W => f ⁻¹' W) hj
  have hsame : i' = j' := SimultaneousNormalCrossings.eq_of_eventually_mem_iff
    (isSNCDivisor_preimage_submersion hf E hE)
    (by rw [hi',hpre];exact hz) (by rw [hj'];exact hz)
    (Filter.Eventually.of_forall fun w => by rw [hi',hj',hpre])
  have hval : i.val = j.val := congrArg (fun t : Fin (E.map (f ⁻¹' ·)).length => t.val) hsame
  have hij : i = j := Fin.ext hval
  have hHH₀ : H = H₀ := hj.symm.trans ((congrArg E.get hij).symm.trans hi)
  rwa [hHH₀]

/-- The entire original coefficient/member restriction is produced from
the actual smooth map, original well-formed record and original member list. -/
theorem markedPullback_memberRestrict_membersThrough
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (E₀ : List (Set X))
    (hE₀ : ∀ H ∈ E₀, H ∈ M.E) (z : Y) :
    markedPullback (m := m) f (memberRestrict M (membersThrough M.E E₀ (f z))) =
      memberRestrict (markedPullback (m := m) f M)
        (membersThrough (markedPullback (m := m) f M).E (E₀.map (f ⁻¹' ·)) z) := by
  have hc := pullback_coeffMarkedAlong hf M hM.isCoherent hM.isClosedSubmanifold_N
  have hI := congrArg MarkedIdeal.ideal hc
  have hd := congrArg MarkedIdeal.d hc
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ hI hd
  · change f ⁻¹' (memberRestrict M (membersThrough M.E E₀ (f z))).N = _
    rw [memberRestrict_membersThrough_N,memberRestrict_membersThrough_N]
    ext q
    simp only [mem_preimage,mem_inter_iff,mem_ofPred_eq]
    refine and_congr_right fun _ => ⟨fun hw H' hH' hH'₀ hzH' => ?_,
      fun hw H hH hH₀ hzH => ?_⟩
    · obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hH'
      exact hw H hH (mem_of_preimage_mem_map_through hf hM.isSNCDivisor hE₀ hH hzH' hH'₀) hzH'
    · exact hw _ (List.mem_map_of_mem hH) (List.mem_map_of_mem hH₀) hzH
  · change (memberRestrict M (membersThrough M.E E₀ (f z))).E.map (f ⁻¹' ·) = _
    rw [memberRestrict_membersThrough_E,memberRestrict_membersThrough_E]
    exact (filter_map_members (f := (f ⁻¹' ·)) (y := f z) (y' := z)
      (fun H _ => Iff.rfl) fun H hH hzH h =>
        mem_of_preimage_mem_map_through hf hM.isSNCDivisor hE₀ hH hzH h).symm

variable {D : CMfd.{u} n} {D' : CMfd.{u} m}
  {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

/-- The actual positive masked lower record and actual restricted smooth
map are constructed from the original datum and actual Cartesian history. -/
theorem IsActualTowerPullback.exists_actual_positive_lower_record
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) (s : ℕ) (z : D') :
    ∃ p : lowerMask (markedPullback (m := m) f M) (s+1) Q z →
        lowerMask M (s+1) T (g z),
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ p ∧
      (∀ w, (p w : D) = g (w : D')) ∧
      markedPullback (m := m) p (lowerMarkedM M (s+1) T (g z)) =
        lowerMarkedM (markedPullback (m := m) f M) (s+1) Q z := by
  let V := maskA (markedPullback (m := m) f M) Q z
  let U := maskA M T (g z)
  have hV := IsActualTowerPullback.all_maskA_dictionary h M hM hT z
  have hVU : MapsTo g V U := by
    intro w hw
    change w ∈ (maskA (markedPullback (m := m) f M) Q z : Set D') at hw
    rw [hV] at hw
    exact hw
  let p : V → U := restrictedOpenMap V U hVU
  have hp := restrictedOpenMap_isSubmersion h.isSubmersion V U hVU
  have hMT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked M hM) T hT
  let J := memberRestrict (geoTransformAlong (barMarked M) T)
    (membersThrough (geoTransformAlong (barMarked M) T).E (origMembers M T) (g z))
  have hc : J.ideal.IsCoherent := by
    change (memberRestrict _ _).ideal.IsCoherent
    rw [memberRestrict_ideal]
    exact isCoherent_coeffMarkedAlong hMT.isCoherent hMT.isClosedSubmanifold_N
  have hJ : memberRestrict (geoTransformAlong (barMarked (markedPullback (m := m) f M)) Q)
      (membersThrough (geoTransformAlong (barMarked (markedPullback (m := m) f M)) Q).E
        (origMembers (markedPullback (m := m) f M) Q) z) = markedPullback (m := m) g J := by
    rw [(IsActualTowerPullback.bar_stage_dictionary h M hM hT).2,
      IsActualTowerPullback.bar_original_members_dictionary h M hM hT]
    exact (markedPullback_memberRestrict_membersThrough h.isSubmersion _ hMT _
      (fun H hH => List.mem_of_mem_take hH) z).symm
  refine ⟨p,hp,fun _ => rfl,?_⟩
  change markedPullback (m := m) p
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → D) J) =
    MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : V → D')
      (memberRestrict (geoTransformAlong (barMarked (markedPullback (m := m) f M)) Q)
        (membersThrough (geoTransformAlong (barMarked (markedPullback (m := m) f M)) Q).E
          (origMembers (markedPullback (m := m) f M) Q) z))
  rw [hJ]
  change markedPullback (m := m) p
      (markedPullback (m := n) (Subtype.val : U → D) J) =
    markedPullback (m := m) (Subtype.val : V → D') (markedPullback (m := m) g J)
  rw [← whole_parameter_markedPullback_comp (X := D) (Y := CMfd.of (n := n) U)
      (Z := CMfd.of (n := m) V) (f := (Subtype.val : U → D)) (g := p)
      contMDiff_subtype_val hp.contMDiff J hc,
    ← whole_parameter_markedPullback_comp (X := D) (Y := D')
      (Z := CMfd.of (n := m) V) (f := g) (g := (Subtype.val : V → D'))
      h.isSubmersion.contMDiff contMDiff_subtype_val J hc]
  rfl

/-- Both actual split histories, full original positive lower records and
whole actual restricted lower tails are produced at any literal split. -/
theorem IsActualTowerPullback.exists_split_actual_positive_lower_diagram
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) (j s : ℕ) (z : D') :
    ∃ a : (split Q j).1 → (split T j).1,
      IsActualTowerPullback f (head Q j) (head T j) a ∧
      IsActualTowerPullback a (tail Q j) (tail T j) g ∧
      ∃ (p : lowerMask (markedPullback (m := m) f M) (s+1) (head Q j) ((tail Q j).proj z) →
          lowerMask M (s+1) (head T j) ((tail T j).proj (g z)))
        (q : openPreimage (tail Q j)
          (lowerMask (markedPullback (m := m) f M) (s+1) (head Q j) ((tail Q j).proj z)) →
          openPreimage (tail T j) (lowerMask M (s+1) (head T j) ((tail T j).proj (g z)))),
        Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ p ∧
        (∀ w, (p w : (split T j).1) = a (w : (split Q j).1)) ∧
        (∀ w, (q w : D) = g (w : D')) ∧
        markedPullback (m := m) p
          (lowerMarkedM M (s+1) (head T j) ((tail T j).proj (g z))) =
          lowerMarkedM (markedPullback (m := m) f M) (s+1) (head Q j) ((tail Q j).proj z) ∧
        IsActualTowerPullback p
          (restrict (lowerMask (markedPullback (m := m) f M) (s+1) (head Q j) ((tail Q j).proj z))
            (tail Q j))
          (restrict (lowerMask M (s+1) (head T j) ((tail T j).proj (g z))) (tail T j)) q := by
  obtain ⟨a,hhead,htail⟩ := IsActualTowerPullback.simultaneous_split h j
  have hheadT := ((isGeoTestTower_iff_head_tail (barMarked M) T j).mp hT).1
  have hpoint := htail.proj_comm z
  have hrec := IsActualTowerPullback.exists_actual_positive_lower_record
    hhead M hM hheadT s ((tail Q j).proj z)
  rw [← hpoint] at hrec
  obtain ⟨p₀,hp₀,hpcoord,hrecord⟩ := hrec
  let V := lowerMask (markedPullback (m := m) f M) (s+1) (head Q j) ((tail Q j).proj z)
  let U := lowerMask M (s+1) (head T j) ((tail T j).proj (g z))
  have hV : (V : Set (split Q j).1) = a ⁻¹' (U : Set (split T j).1) := by
    dsimp only [V,U,lowerMask]
    rw [IsActualTowerPullback.all_maskA_dictionary hhead M hM hheadT,← hpoint]
  obtain ⟨p,q,hp,hq,hR⟩ := IsActualTowerPullback.exists_actual_open_restriction htail U V hV
  have hpSame : p₀ = p := by
    funext w
    exact Subtype.ext ((hpcoord w).trans (hp w).symm)
  subst p₀
  exact ⟨a,hhead,htail,p,q,hp₀,hp,hq,hrecord,hR⟩

/-- The literal current positive-level run and actual selected lower
diagram, with no caller run, lower-record or restricted-history certificate. -/
theorem IsActualTowerPullback.exists_selected_actual_positive_lower_diagram
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) (s : ℕ) (z : D')
    (hlevel : level M T (g z) = s+1) :
    let r := StepOneRegime.regimeRun (stepRegime M (level M T (g z))) T (g z)
    StepOneRegime.regimeRun
      (stepRegime (markedPullback (m := m) f M) (level (markedPullback (m := m) f M) Q z)) Q z = r ∧
    ∃ a : (split Q r).1 → (split T r).1,
      IsActualTowerPullback f (head Q r) (head T r) a ∧
      IsActualTowerPullback a (tail Q r) (tail T r) g ∧
      ∃ (p : lowerMask (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z) →
          lowerMask M (s+1) (head T r) ((tail T r).proj (g z)))
        (q : openPreimage (tail Q r)
          (lowerMask (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)) →
          openPreimage (tail T r) (lowerMask M (s+1) (head T r) ((tail T r).proj (g z)))),
        Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ p ∧
        (∀ w, (p w : (split T r).1) = a (w : (split Q r).1)) ∧
        (∀ w, (q w : D) = g (w : D')) ∧
        markedPullback (m := m) p
          (lowerMarkedM M (s+1) (head T r) ((tail T r).proj (g z))) =
          lowerMarkedM (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z) ∧
        IsActualTowerPullback p
          (restrict (lowerMask (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z))
            (tail Q r))
          (restrict (lowerMask M (s+1) (head T r) ((tail T r).proj (g z))) (tail T r)) q := by
  dsimp only
  constructor
  · rw [IsActualTowerPullback.bar_level_dictionary h M hM hT z,hlevel]
    exact IsActualTowerPullback.all_stepRegime_run h M hM hT (s+1) z
  · exact IsActualTowerPullback.exists_split_actual_positive_lower_diagram h M hM hT _ s z

end
end Hironaka.HironakaSmoothSubmersionPositiveLowerHistory
