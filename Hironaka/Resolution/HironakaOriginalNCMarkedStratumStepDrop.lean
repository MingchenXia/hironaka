import Hironaka.Resolution.HironakaOriginalNCMarkedStratumCanonicalHistory
import Hironaka.Invariant.StepOnePhase
import Hironaka.Invariant.GeneralPhaseCount

/-!
# The NEW prescribed-H marked-stratum value: StepDrop and growing sequences

The native carrier is arbitrary.  The given raw NEW-Psi canonical histories
internally produce ordinary tests, all original branch histories, and the
actual common marked-stratum phase.  No future or desired-decrease certificate
is an input.  The static private-proof export below reuses one existing typed
geometric proof; it does not inspect or mutate the environment.

Mathematics first: mathematical-field-design.tex and the complete native API
inventory in work/hironaka-g9-new-marked-stratum-driver-fields-20261023/
resume-20261024/.  This is an initial SOURCE-ONLY draft: it has not been Lean
checked and adds no Blueprint credit, complete invariant installation,
noncompact resolving sequence, terminal NC theorem or original-goal closure.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCMarkedStratumStepDrop

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdealRestrictOpen
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  NormalCrossings HomogenizedGlueingTower MemberInterTowerAlong
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaOriginalOldBranchOpenHistory HironakaOriginalNCCountHistory
  HironakaOriginalNCCausalHistoryValue HironakaOriginalNCCausalEmptyState
  HironakaOriginalNCOldStratumStrictEquality HironakaOriginalNCMarkedStratum
  HironakaOriginalNCMarkedStratumHistoryValue HironakaOriginalNCMarkedStratumBranchHistory
  HironakaOriginalNCMarkedStratumBirthFrame HironakaOriginalNCMarkedStratumCanonicalHistory
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/- This fixed literal name becomes an ordinary term identifier.  It names the
exact geometric mother whose complete type, source proof and digest are saved
in the mathematical/API inventory.  There is no helper argument or lookup for
an arbitrary desired proof, and no new mathematical credit for this wrapper. -/
macro "markedEmptyPhaseProof%" : term =>
  pure <| Lean.mkIdent <| Lean.mkPrivateNameCore
    `Hironaka.Resolution.HironakaOriginalNCMarkedStratumCanonicalHistory
    `Hironaka.HironakaOriginalNCMarkedStratumCanonicalHistory.empty_birth_state_after_phase

private theorem lower_birth_tails_of_actual_frame
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (f : MarkedStratumPhaseFrame M H T) :
    ∀ y ∈ (geoTransformAlong M T).cosupp, oldCount H T y < f.q →
      IsEmptyTower (causalBirthTail H T y) := by
  rcases f with ⟨B, K, P, hEq, hK, hHistoryK, hEmptyK, q, _hCover,
    hP, hHistoryP, hHigh, _hBound, _hAttained, _hCan⟩
  subst T
  exact (markedEmptyPhaseProof%) M hM h K hK hHistoryK hEmptyK q P hP hHistoryP hHigh

private theorem branch_count_of_carrier_eq {B : Type u} [TopologicalSpace B]
    [ChartedSpace (ComplexModel n) B] {F G : Set B}
    (hF : IsNormalCrossingsCarrier (n := n) F) (hG : IsNormalCrossingsCarrier (n := n) G)
    (he : F = G) (x : B) : branchMultiplicity hF x = branchMultiplicity hG x := by
  subst G
  rfl

private theorem old_count_step_eq_off_centre
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hNext : IsGeoTestTower M (.step T C π hπ))
    (hHistoryNext : IsOriginalBranchTestTower M H (.step T C π hπ))
    (hHistory : IsOriginalBranchTestTower M H T) (z : Z) (hz : π z ∉ C) :
    oldCount H (.step T C π hπ) z = oldCount H T (π z) := by
  have hTD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hNext.1
  let hcRaw := (current_old_strata_eq_strict M h T hNext.1 hHistory).1
  let hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E :=
    ⟨hcRaw.1, hTD.isWellFormed.isSNCDivisor.1, hcRaw.2.2⟩
  let hc' := (current_old_strata_eq_strict M h (.step T C π hπ) hNext hHistoryNext).1
  let U : Opens Y := ⟨Cᶜ, hπ.1.1.isOpen_compl⟩
  let P : BlowupTower Y Z := .step .refl C π hπ
  let D := openPreimage P U
  let HU := (Subtype.val : U → Y) ⁻¹' strictAlong T H
  let h0 := isNormalCrossingsCarrier_of_boundaryAdapted hc
  let h1 := isNormalCrossingsCarrier_of_boundaryAdapted hc'
  let hU := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open U hc)
  let hD := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open D hc')
  have hEmpty : IsEmptyTower (restrict U P) := by
    change True ∧ (Subtype.val : U → Y) ⁻¹' C = ∅
    refine ⟨trivial, eq_empty_iff_forall_notMem.mpr ?_⟩
    intro p hp
    exact p.property hp
  have hOld : strictAlong (restrict U P) HU =
      (Subtype.val : D → Z) ⁻¹' strictAlong (.step T C π hπ) H := by
    rw [strictAlong_restrict U P (strictAlong T H)]
    rfl
  have hND : IsNormalCrossingsCarrier (n := n) (strictAlong (restrict U P) HU) := hOld.symm ▸ hD
  let p : D := ⟨z, hz⟩
  have hCount := HironakaOriginalOldBranchCountDrop.branchMultiplicity_empty_tower
    hU (restrict U P) hEmpty hND p
  have hEq : branchMultiplicity hND p = branchMultiplicity hD p :=
    branch_count_of_carrier_eq hND hD hOld p
  calc
    _ = branchMultiplicity h1 z := oldCount_eq _ h1 z
    _ = branchMultiplicity hD p := (branchMultiplicity_open D h1 hD p).symm
    _ = branchMultiplicity hND p := hEq.symm
    _ = branchMultiplicity hU ((restrict U P).proj p) := hCount
    _ = branchMultiplicity h0 (π z) := branchMultiplicity_open U h0 hU ((restrict U P).proj p)
    _ = oldCount H T (π z) := (oldCount_eq T h0 (π z)).symm

private theorem lower_empty_step_mask_value
    (A : MarkedIdeal n X) (hA : IsInvDomain n A) (S : BlowupTower X Y)
    (hCan : IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) S)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) (hC : C = ∅) (z : Z) :
    (if z ∈ (geoTransformAlong A (.step S C π hπ)).cosupp then
      ((CanonicalCentres.canonicalInvariant n).inv A (.step S C π hπ) z : WithBot (CanonicalCentres.ValTy n)) else ⊥) =
    (if π z ∈ (geoTransformAlong A S).cosupp then
      ((CanonicalCentres.canonicalInvariant n).inv A S (π z) : WithBot (CanonicalCentres.ValTy n)) else ⊥) := by
  let R := CanonicalCentres.canonicalInvariant n
  have hTest := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical R.isInvValue hA S hCan
  have hW := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent S hTest
  have hOff : π z ∉ C := by rw [hC]; exact notMem_empty _
  have hMask : z ∈ (geoTransformAlong A (.step S C π hπ)).cosupp ↔
      π z ∈ (geoTransformAlong A S).cosupp :=
    TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong A S) hW.1.1
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hW.2 hg) hπ hOff
  by_cases hz : z ∈ (geoTransformAlong A (.step S C π hπ)).cosupp
  · have hp := hMask.mp hz
    have hv := R.isInvValue.emptyStep A hA S C π hπ hC hCan z hz
    rw [if_pos hz, if_pos hp, hv]
  · have hp : π z ∉ (geoTransformAlong A S).cosupp := fun hh => hz (hMask.mpr hh)
    rw [if_neg hz, if_neg hp]

private theorem value_step_of_empty_birth_centre
    (M : MarkedIdeal n X) (H : Set X) (T : BlowupTower X Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) (z : Z)
    (he : oldCount H (.step T C π hπ) z = oldCount H T (π z))
    (hA : IsInvDomain n (markedStratumBirth M H T (π z)))
    (hS : IsCanonical (markedStratumBirth M H T (π z))
      ((CanonicalCentres.canonicalInvariant n).inv (markedStratumBirth M H T (π z)))
      (causalBirthTail H T (π z)))
    (hCentre : (Subtype.val : openPreimage (tail T (T.length - birthYear H T (π z)))
      (causalBirthOpen H T (π z)) → Y) ⁻¹' C = ∅) :
    markedStratumHistoryValue M H (.step T C π hπ) z = markedStratumHistoryValue M H T (π z) := by
  let x := π z
  let W := causalBirthOpen H T x
  let D := tail T (T.length - birthYear H T x)
  let A := markedStratumBirth M H T x
  let S := causalBirthTail H T x
  let J := openPreimage D W
  let P : BlowupTower Y Z := .step .refl C π hπ
  let J' := openPreimage (.step D C π hπ) W
  let Cw := (Subtype.val : J → Y) ⁻¹' C
  let πw : J' → J := fun p => ⟨π p.val, p.property⟩
  have hπw : IsBlowupAlong n Cw πw :=
    BlowupRestrictOpen.isBlowupAlong_restrict hπ J (J.isOpen.preimage hπ.contMDiff.continuous)
  let S' : BlowupTower (CMfd.of (n := n) W) (CMfd.of (n := n) J') := .step S Cw πw hπw
  have hCw : Cw = ∅ := hCentre
  let p : J' := ⟨z, (causalBirthPoint H T x).property⟩
  let p0 := causalBirthPoint H T x
  have hp0 : πw p = p0 := Subtype.ext rfl
  have hMaskValue := lower_empty_step_mask_value (X := CMfd.of (n := n) W)
    (Y := CMfd.of (n := n) J) (Z := CMfd.of (n := n) J') A hA S hS Cw πw hπw hCw p
  rw [hp0] at hMaskValue
  have hNew := markedStratumHistoryValue_append_of_count_eq M H T P z he
  let R := CanonicalCentres.canonicalInvariant n
  change markedStratumHistoryValue M H (.step T C π hπ) z =
    toLex (oldCount H T x, if p ∈ (geoTransformAlong A S').cosupp then
      (R.inv A S' p : WithBot (CanonicalCentres.ValTy n)) else ⊥) at hNew
  have hOld : markedStratumHistoryValue M H T x =
      toLex (oldCount H T x, if p0 ∈ (geoTransformAlong A S).cosupp then
        (R.inv A S p0 : WithBot (CanonicalCentres.ValTy n)) else ⊥) := rfl
  rw [hNew, hOld]
  exact congrArg (fun v : WithBot (CanonicalCentres.ValTy n) => toLex (oldCount H T x, v)) hMaskValue

private theorem centre_misses_lower_birth_window
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (x : Y)
    (hEmpty : IsEmptyTower (causalBirthTail H T x)) (q : ℕ)
    (hLow : oldCount H T x < q) (C : Set Y)
    (hHigh : ∀ c ∈ C, q ≤ oldCount H T c) :
    (Subtype.val : openPreimage (tail T (T.length - birthYear H T x))
      (causalBirthOpen H T x) → Y) ⁻¹' C = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hb := (empty_birth_window M hM h T hT hHistory x hEmpty).2.2.2.2 p
  have hc := hHigh p.val hp
  omega

private theorem canonical_centre_is_high
    (M : MarkedIdeal n X) (H : Set X) (T : BlowupTower X Y)
    (f : MarkedStratumPhaseFrame M H T) (C : Set Y)
    (hChoice : C = ∅ ∨ C = ResolutionDriver.maxLocus (markedStratumHistoryValue M H T)
      (geoTransformAlong M T).cosupp) :
    C ⊆ (geoTransformAlong M T).cosupp ∧ ∀ c ∈ C, f.q ≤ oldCount H T c := by
  rcases hChoice with rfl | hC
  · exact ⟨empty_subset _, fun _ hc => False.elim hc⟩
  rw [hC]
  refine ⟨fun _ hy => hy.1, ?_⟩
  intro c hc
  obtain ⟨x, hx, hxq⟩ := f.attained
  have hh := hc.2 x hx
  change toLex (oldCount H T x, _) ≤ toLex (oldCount H T c, _) at hh
  rw [Prod.Lex.toLex_le_toLex] at hh
  rcases hh with hl | ⟨he, _⟩ <;> omega

private theorem step_drop_in_actual_marked_stratum_phase
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hCan : IsCanonical M (markedStratumHistoryValue M H) T)
    (f : MarkedStratumPhaseFrame M H T)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hChoice : C = ∅ ∨ C = ResolutionDriver.maxLocus (markedStratumHistoryValue M H T)
      (geoTransformAlong M T).cosupp) :
    ∀ z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp,
      (π z ∈ C → markedStratumHistoryValue M H (.step T C π hπ) z < markedStratumHistoryValue M H T (π z)) ∧
      (π z ∉ C → markedStratumHistoryValue M H (.step T C π hπ) z = markedStratumHistoryValue M H T (π z)) := by
  obtain ⟨hTest, hHistory, hBirth, _⟩ := markedStratum_canonical_history_joint_interpretation M hM h T hCan
  obtain ⟨hNext, hHistoryNext, _hBirthNext, _⟩ :=
    markedStratum_canonical_history_joint_interpretation M hM h (.step T C π hπ) ⟨hCan, hChoice⟩
  have hMax := MarkedStratumPhaseFrame.whole_maximum M hM h T f
  have hLower := lower_birth_tails_of_actual_frame M hM h T f
  obtain ⟨hCos, hCentreHigh⟩ := canonical_centre_is_high M H T f C hChoice
  rcases f with ⟨B, K, P, hTKP, hK, hHistoryK, hEmptyK, q, hCover,
    hP, hHistoryP, _hHigh, hCurrentBound, _hAttained, hCanQ⟩
  subst T
  let V := oldCountLowOpen H K q
  let MC := geoTransformAlong M K
  let A := phaseAuxiliary M H K q
  let R := CanonicalCentres.canonicalInvariant n
  let U := openPreimage P V
  let Pnext : BlowupTower B Z := .step P C π hπ
  let U' := openPreimage Pnext V
  let Q := restrict V P
  let Qnext := restrict V Pnext
  let Cq : Set U := (Subtype.val : U → Y) ⁻¹' C
  let πv : U' → U := fun p => ⟨π p.val, p.property⟩
  have hπv : IsBlowupAlong n Cq πv :=
    BlowupRestrictOpen.isBlowupAlong_restrict hπ U (U.isOpen.preimage hπ.contMDiff.continuous)
  have hQnext : Qnext = .step Q Cq πv hπv := rfl
  have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hK
  have hA := (phaseAuxiliary_domain M hM h K hK hHistoryK q).1
  have hLocalChoice : Cq = ∅ ∨ Cq = ResolutionDriver.maxLocus (R.inv A Q)
      (geoTransformAlong A Q).cosupp := by
    by_cases hCEmpty : C = ∅
    · exact Or.inl (by simp only [Cq, hCEmpty, preimage_empty])
    · right
      have hCM : C = (Subtype.val : U → Y) ''
          ResolutionDriver.maxLocus (R.inv A Q) (geoTransformAlong A Q).cosupp :=
        (hChoice.resolve_left hCEmpty).trans hMax
      ext p
      constructor
      · intro hp
        have hpC : p.val ∈ C := hp
        rw [hCM] at hpC
        obtain ⟨w, hw, he⟩ := hpC
        exact (Subtype.ext he : w = p) ▸ hw
      · intro hp
        change p.val ∈ C
        rw [hCM]
        exact ⟨p, hp, rfl⟩
  have hCanQnext : IsCanonical A (R.inv A) Qnext := by
    change IsCanonical A (R.inv A) Q ∧ _
    exact ⟨hCanQ, hLocalChoice⟩
  have hATest := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical R.isInvValue hA Q hCanQ
  have hATestNext := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical R.isInvValue hA Qnext hCanQnext
  have hPNext : IsGeoTestTower MC Pnext := ((isGeoTestTower_append_iff M K Pnext).mp hNext).2
  have hLocalHistory := (phase_local_test_history M hM h K hK hHistoryK q Pnext hATestNext).2
  have hHistoryPNext : IsOriginalBranchTestTower MC (strictAlong K H) Pnext :=
    isOriginalBranchTestTower_of_restrict_cosupport_cover MC hKD.isWellFormed.isClosedSubmanifold_N
      hKD.isWellFormed.isCoherent V hCover Pnext hPNext hLocalHistory
  have hOldCos := phase_whole_cosupp M hM h K hK hHistoryK q P hP hHistoryP hATest
  have hNewCos := phase_whole_cosupp M hM h K hK hHistoryK q Pnext hPNext hHistoryPNext hATestNext
  have hOldCover (y : Y) (hy : y ∈ (geoTransformAlong M (K.append P)).cosupp) : y ∈ U := by
    have hy' : y ∈ (geoTransformAlong MC P).cosupp := by simpa only [MC, geoTransformAlong_append] using hy
    exact hCover (TransformOffCentre.cosupp_geoTransformAlong_subset MC
      hKD.isWellFormed.isClosedSubmanifold_N hKD.isWellFormed.isCoherent P hP hy')
  have hNewCover (z : Z) (hz : z ∈ (geoTransformAlong M (K.append Pnext)).cosupp) : z ∈ U' := by
    have hz' : z ∈ (geoTransformAlong MC Pnext).cosupp := by simpa only [MC, geoTransformAlong_append] using hz
    exact hCover (TransformOffCentre.cosupp_geoTransformAlong_subset MC
      hKD.isWellFormed.isClosedSubmanifold_N hKD.isWellFormed.isCoherent Pnext hPNext hz')
  intro z hz
  have hx : π z ∈ (geoTransformAlong M (K.append P)).cosupp :=
    StepOneWellFounded.proj_mem_cosupp_step hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent (K.append P) C π hπ hNext hz
  have hAnti := oldCount_step_le_native M hM.isWellFormed h (K.append P) C π hπ hNext hHistoryNext z
  have hBoundNew : oldCount H (K.append Pnext) z ≤ q := hAnti.trans (hCurrentBound (π z) hx)
  let p : U' := ⟨z, hNewCover z hz⟩
  let p0 : U := ⟨π z, hOldCover (π z) hx⟩
  have hProj : πv p = p0 := Subtype.ext rfl
  constructor
  · intro hzC
    have hxq : oldCount H (K.append P) (π z) = q :=
      le_antisymm (hCurrentBound (π z) hx) (hCentreHigh _ hzC)
    by_cases hDrop : oldCount H (K.append Pnext) z < q
    · change toLex (oldCount H (K.append Pnext) z, _) < toLex (oldCount H (K.append P) (π z), _)
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl (hxq ▸ hDrop)
    · have hzq : oldCount H (K.append Pnext) z = q := by omega
      have hp0C : p0 ∈ Cq := hzC
      have hCqNe : Cq.Nonempty := ⟨p0, hp0C⟩
      have hCqMax := hLocalChoice.resolve_left (Set.nonempty_iff_ne_empty.mp hCqNe)
      have hp0A : p0 ∈ (geoTransformAlong A Q).cosupp := by
        rw [hOldCos]
        exact ⟨hx, hxq⟩
      have hpA : p ∈ (geoTransformAlong A Qnext).cosupp := by
        rw [hNewCos]
        exact ⟨hz, hzq⟩
      have ho := (phase_value_at_top M hM h K hK hHistoryK hEmptyK q hCover P hP hHistoryP hCanQ p0 hx hxq).2
      have hn := (phase_value_at_top M hM h K hK hHistoryK hEmptyK q hCover Pnext hPNext hHistoryPNext hCanQnext p hz hzq).2
      rw [if_pos hp0A] at ho
      rw [if_pos hpA] at hn
      have hDec := R.isInvValue.decrease (X := CMfd.of (n := n) V) (Y := CMfd.of (n := n) U)
        (Z := CMfd.of (n := n) U') A hA Q Cq πv hπv hCanQ hCqNe hCqMax p
        (by simpa only [hQnext] using hpA)
      rw [← hQnext, hProj] at hDec
      change markedStratumHistoryValue M H (K.append Pnext) p.val < markedStratumHistoryValue M H (K.append P) p0.val
      rw [hn, ho, Prod.Lex.toLex_lt_toLex]
      exact Or.inr ⟨rfl, WithBot.coe_lt_coe.mpr (hDec.1 hp0C)⟩
  · intro hzC
    have he := old_count_step_eq_off_centre M hM h (K.append P) C π hπ hNext hHistoryNext hHistory z hzC
    by_cases hLow : oldCount H (K.append P) (π z) < q
    · have hEmpty := hLower (π z) hx hLow
      have hMiss := centre_misses_lower_birth_window M hM h (K.append P) hTest hHistory (π z)
        hEmpty q hLow C hCentreHigh
      obtain ⟨hBirthA, hBirthS, _⟩ := hBirth (π z) hx
      exact value_step_of_empty_birth_centre M H (K.append P) C π hπ z he hBirthA hBirthS hMiss
    · have hxq : oldCount H (K.append P) (π z) = q := by
        have hb := hCurrentBound (π z) hx
        omega
      have hzq : oldCount H (K.append Pnext) z = q := he.trans hxq
      have hp0Off : p0 ∉ Cq := hzC
      have hp0A : p0 ∈ (geoTransformAlong A Q).cosupp := by
        rw [hOldCos]
        exact ⟨hx, hxq⟩
      have hpA : p ∈ (geoTransformAlong A Qnext).cosupp := by
        rw [hNewCos]
        exact ⟨hz, hzq⟩
      have ho := (phase_value_at_top M hM h K hK hHistoryK hEmptyK q hCover P hP hHistoryP hCanQ p0 hx hxq).2
      have hn := (phase_value_at_top M hM h K hK hHistoryK hEmptyK q hCover Pnext hPNext hHistoryPNext hCanQnext p hz hzq).2
      rw [if_pos hp0A] at ho
      rw [if_pos hpA] at hn
      have hVal : R.inv A Qnext p = R.inv A Q p0 := by
        by_cases hCqEmpty : Cq = ∅
        · have hv := R.isInvValue.emptyStep (X := CMfd.of (n := n) V) (Y := CMfd.of (n := n) U)
            (Z := CMfd.of (n := n) U') A hA Q Cq πv hπv hCqEmpty hCanQ p
            (by simpa only [hQnext] using hpA)
          simpa only [← hQnext, hProj] using hv
        · have hCqMax := hLocalChoice.resolve_left hCqEmpty
          have hv := R.isInvValue.decrease (X := CMfd.of (n := n) V) (Y := CMfd.of (n := n) U)
            (Z := CMfd.of (n := n) U') A hA Q Cq πv hπv hCanQ
            (Set.nonempty_iff_ne_empty.mpr hCqEmpty) hCqMax p
            (by simpa only [hQnext] using hpA)
          rw [← hQnext, hProj] at hv
          exact hv.2 hp0Off
      change markedStratumHistoryValue M H (K.append Pnext) p.val = markedStratumHistoryValue M H (K.append P) p0.val
      rw [hn, ho, hVal]

/-- The actual existing StepDrop predicate for the DEFINED NEW proper-carrier
value.  Its only natural inputs are the native original domain and prescribed
H-adaptation; all test/history/phase/lower canonical data are internal. -/
theorem markedStratum_history_value_stepDrop
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E) :
    StepOneWellFounded.StepDrop M (markedStratumHistoryValue M H) := by
  intro Y Z T C π hπ hCanNext z hz
  obtain ⟨hCanT, hChoice⟩ := hCanNext
  obtain ⟨_hT, _hHistory, _hBirth, hFrames⟩ :=
    markedStratum_canonical_history_joint_interpretation M hM h T hCanT
  obtain ⟨hNext, _hHistoryNext, _, _⟩ :=
    markedStratum_canonical_history_joint_interpretation M hM h (.step T C π hπ) ⟨hCanT, hChoice⟩
  have hx := StepOneWellFounded.proj_mem_cosupp_step hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent T C π hπ hNext hz
  obtain ⟨f⟩ := hFrames ⟨π z, hx⟩
  exact ⟨hx, step_drop_in_actual_marked_stratum_phase M hM h T hCanT f C π hπ hChoice z hz⟩

/-- True ANY-growing-sequence counts, for the prescribed H and the NEW value.
The conclusion even holds for arbitrary K.  This does not construct a
noncompact resolving history or prove terminal NC/G3 scheduling. -/
theorem markedStratum_history_value_growing_sequence_bound
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (s : ResolutionInvariantSeq.GrowingSeq X)
    (hs : ∀ i, IsCanonical M (markedStratumHistoryValue M H) (s.stage i).2)
    (K : Set X) :
    ∃ m : ℕ, ∀ i, ResolutionInvariantSpec.countCentresMeeting K (s.stage i).2 ≤ m := by
  let inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) :=
    fun {_Y} T y => markedStratumHistoryValue M H T y
  have hDrop : StepOneWellFounded.StepDrop M inv := markedStratum_history_value_stepDrop M hM h
  obtain ⟨m, hm⟩ := GeneralPhaseCount.exists_bound_of_isPrefix
    (fun i => StepOnePhase.centreValues inv (s.stage i).2)
    (fun i => GeneralPhaseCount.centreValues_isPrefix_succ inv s i)
    (fun i => StepOnePhase.pairwise_centreValues hDrop _ (hs i))
    (fun _ => True) (fun _ _ _ => trivial) (fun g _ => not_strictAnti_of_wellFoundedLT g)
  exact ⟨m, fun i => (StepOnePhase.countCentresMeeting_le_length_centreValues inv K (s.stage i).2).trans (hm i)⟩

/-- The exact empty-step numerical field follows from the same natural
StepDrop theorem, without changing the given history or erasing empty years. -/
theorem markedStratum_history_value_empty_step
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hC : C = ∅) (hCan : IsCanonical M (markedStratumHistoryValue M H) T)
    (z : Z) (hz : z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp) :
    markedStratumHistoryValue M H (.step T C π hπ) z = markedStratumHistoryValue M H T (π z) := by
  have hDrop := markedStratum_history_value_stepDrop M hM h T C π hπ ⟨hCan, Or.inl hC⟩ z hz
  exact hDrop.2.2 (by rw [hC]; exact notMem_empty _)

/-- The native nonempty-whole-maximum decrease field, at the exact original
marked ideal and prescribed H.  No additional phase or future premise. -/
theorem markedStratum_history_value_decrease
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCan : IsCanonical M (markedStratumHistoryValue M H) T) (_hCNe : C.Nonempty)
    (hC : C = ResolutionDriver.maxLocus (markedStratumHistoryValue M H T) (geoTransformAlong M T).cosupp)
    (z : Z) (hz : z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp) :
    (π z ∈ C → markedStratumHistoryValue M H (.step T C π hπ) z < markedStratumHistoryValue M H T (π z)) ∧
      (π z ∉ C → markedStratumHistoryValue M H (.step T C π hπ) z = markedStratumHistoryValue M H T (π z)) := by
  exact (markedStratum_history_value_stepDrop M hM h T C π hπ ⟨hCan, Or.inr hC⟩ z hz).2

end
end Hironaka.HironakaOriginalNCMarkedStratumStepDrop
