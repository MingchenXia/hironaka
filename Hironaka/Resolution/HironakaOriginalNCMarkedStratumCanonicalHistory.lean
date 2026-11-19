import Hironaka.Resolution.HironakaOriginalNCMarkedStratumBirthFrame
import Hironaka.Resolution.HironakaOriginalNCCausalEmptyState

/-!
# The NEW proper-carrier marked-stratum canonical joint interpreter

The natural public producer is implemented by simultaneous induction on the
GIVEN raw Psi-canonical tower. Native tests, ALL original branch histories,
SAME birth lower canonical tails, and the common literal phase are conclusions.
No future test/history/canonical/cosupport/phase certificate is a caller input.
This is an initial source-only implementation. No Lean/kernel acceptance,
new invariant fields or complete G9 closure is claimed.
Math first: joint-frame-design.md and literal-restriction addendum.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCMarkedStratumCanonicalHistory

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerSplitIso
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealTowerTransport MarkedIdealEquivalence.MarkedIdeal
  NormalCrossings HomogenizedGlueingTower MemberInterTowerAlong
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaOriginalOldBranchOpenHistory HironakaOriginalNCCountHistory
  HironakaOriginalNCCausalHistoryValue HironakaOriginalNCCausalEmptyState
  HironakaOriginalNCOldStratumStrictEquality HironakaOriginalNCMarkedStratum
  HironakaOriginalNCMarkedStratumHistoryValue HironakaOriginalNCMarkedStratumBranchHistory
  HironakaOriginalNCMarkedStratumBirthFrame
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)

variable {n : ℕ} {X Y Z : CMfd.{u} n}

private theorem birthYear_step_eq_of_count_eq {C : Set Y} {π : Z → Y}
    (T : BlowupTower X Y) (hπ : IsBlowupAlong n C π) (H : Set X) (y : Z)
    (he : oldCount H (.step T C π hπ) y = oldCount H T (π y)) :
    birthYear H (.step T C π hπ) y = birthYear H T (π y) := by
  have hb := birthYear_le_length H T (π y)
  have hLe : birthYear H (.step T C π hπ) y ≤ birthYear H T (π y) := by
    apply Nat.find_min'
    simpa only [countAt, if_pos hb, he] using birthYear_spec H T (π y)
  have hNewLe : birthYear H (.step T C π hπ) y ≤ T.length := hLe.trans hb
  apply le_antisymm hLe
  apply Nat.find_min'
  simpa only [countAt, if_pos hNewLe, he] using birthYear_spec H (.step T C π hπ) y

private theorem birthYear_step_eq_length_of_count_drop {C : Set Y} {π : Z → Y}
    (T : BlowupTower X Y) (hπ : IsBlowupAlong n C π) (H : Set X) (y : Z)
    (hAnti : Antitone (countAt H T (π y)))
    (hDrop : oldCount H (.step T C π hπ) y < oldCount H T (π y)) :
    birthYear H (.step T C π hπ) y = (BlowupTower.step T C π hπ).length := by
  have hMax := birthYear_le_length H (.step T C π hπ) y
  have hNot : ¬ birthYear H (.step T C π hπ) y ≤ T.length := by
    intro hb
    have hs := birthYear_spec H (.step T C π hπ) y
    simp only [countAt, if_pos hb] at hs
    have hLower : oldCount H T (π y) ≤ countAt H T (π y) (birthYear H (.step T C π hπ) y) :=
      (countAt_length H T (π y)).symm.trans_le (hAnti hb)
    omega
  rw [BlowupTower.length_step] at hMax ⊢
  omega


private theorem empty_birth_state_step
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hStep : IsGeoTestTower M (.step T C π hπ))
    (hHistoryStep : IsOriginalBranchTestTower M H (.step T C π hπ))
    (r : ℕ) (hC : ∀ c ∈ C, r ≤ oldCount H T c)
    (hState : ∀ x ∈ (geoTransformAlong M T).cosupp,
      oldCount H T x < r → IsEmptyTower (causalBirthTail H T x)) :
    ∀ y ∈ (geoTransformAlong M (.step T C π hπ)).cosupp,
      oldCount H (.step T C π hπ) y < r → IsEmptyTower (causalBirthTail H (.step T C π hπ) y) := by
  have hHistoryT : IsOriginalBranchTestTower M H T :=
    fun U B hSNC hUnion => (hHistoryStep U B hSNC hUnion).1
  intro y hy hLow
  have hLe := oldCount_step_le_native M hM.isWellFormed h T C π hπ hStep hHistoryStep y
  by_cases he : oldCount H (.step T C π hπ) y = oldCount H T (π y)
  · have hOldLow : oldCount H T (π y) < r := by rw [he] at hLow; exact hLow
    have hTI := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      (𝔪 := M) hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hStep.1
    let U : BlowupTower Y Z := .step .refl C π hπ
    have hU : IsGeoTestTower (geoTransformAlong M T) U := ⟨trivial, hStep.2⟩
    have hx : π y ∈ (geoTransformAlong M T).cosupp :=
      TransformOffCentre.cosupp_geoTransformAlong_subset (geoTransformAlong M T)
        hTI.1 hTI.2 U hU hy
    have hOldEmpty := hState (π y) hx hOldLow
    have hβ := birthYear_step_eq_of_count_eq T hπ H y he
    have hIndex : (BlowupTower.step T C π hπ).length - birthYear H (.step T C π hπ) y =
        (T.length - birthYear H T (π y)) + 1 := by
      rw [BlowupTower.length_step, hβ]
      have hb := birthYear_le_length H T (π y)
      omega
    have hCentreEmpty : (Subtype.val :
        openPreimage (tail T (T.length - birthYear H T (π y))) (causalBirthOpen H T (π y)) → Y) ⁻¹' C = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hb := (empty_birth_window M hM h T hStep.1 hHistoryT (π y) hOldEmpty).2.2.2.2 p
      have hc := hC p.val hp
      omega
    change IsEmptyTower (restrict
      (oldCountLowOpen H (head (.step T C π hπ)
        ((BlowupTower.step T C π hπ).length - birthYear H (.step T C π hπ) y))
        (oldCount H (.step T C π hπ) y))
      (tail (.step T C π hπ)
        ((BlowupTower.step T C π hπ).length - birthYear H (.step T C π hπ) y)))
    rw [hIndex, he]
    change IsEmptyTower (causalBirthTail H T (π y)) ∧
      (Subtype.val : openPreimage (tail T (T.length - birthYear H T (π y)))
        (causalBirthOpen H T (π y)) → Y) ⁻¹' C = ∅
    exact ⟨hOldEmpty, hCentreEmpty⟩
  · have hDrop : oldCount H (.step T C π hπ) y < oldCount H T (π y) := by omega
    have hβ := birthYear_step_eq_length_of_count_drop T hπ H y
      (countAt_antitone_native M hM.isWellFormed h T hStep.1 hHistoryT (π y)) hDrop
    change IsEmptyTower (restrict
      (oldCountLowOpen H (head (.step T C π hπ)
        ((BlowupTower.step T C π hπ).length - birthYear H (.step T C π hπ) y))
        (oldCount H (.step T C π hπ) y))
      (tail (.step T C π hπ)
        ((BlowupTower.step T C π hπ).length - birthYear H (.step T C π hπ) y)))
    rw [hβ, Nat.sub_self]
    trivial
private theorem empty_birth_state_after_phase
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistoryT : IsOriginalBranchTestTower M H T)
    (hState : HasEmptyCausalBirthTails M H T) (r : ℕ) :
    ∀ {Z : CMfd.{u} n} (P : BlowupTower Y Z),
      IsGeoTestTower (geoTransformAlong M T) P →
      IsOriginalBranchTestTower (geoTransformAlong M T) (strictAlong T H) P →
      CentresHaveOldCountAtLeast H T r P →
      ∀ z ∈ (geoTransformAlong M (T.append P)).cosupp,
        oldCount H (T.append P) z < r → IsEmptyTower (causalBirthTail H (T.append P) z)
  | _, .refl, _hP, _hHistoryP, _hHigh => fun z hz _hLow => hState z hz
  | _, .step P C π hπ, hP, hHistoryP, hHigh => by
      have hHistoryPrefix : IsOriginalBranchTestTower (geoTransformAlong M T) (strictAlong T H) P :=
        fun U B hSNC hUnion => (hHistoryP U B hSNC hUnion).1
      have ih := empty_birth_state_after_phase M hM h T hT hHistoryT hState r
        P hP.1 hHistoryPrefix hHigh.1
      have hAppend : IsGeoTestTower M (T.append (.step P C π hπ)) :=
        (isGeoTestTower_append_iff M T (.step P C π hπ)).mpr ⟨hT, hP⟩
      have hHistoryAppend : IsOriginalBranchTestTower M H (T.append (.step P C π hπ)) :=
        original_history_append_native M hM.isWellFormed T (.step P C π hπ) hT hHistoryT hHistoryP
      exact empty_birth_state_step M hM h
        (T.append P) C π hπ hAppend hHistoryAppend r hHigh.2 ih

/-- Actual output/induction data, never a natural caller input. Q is the
literal restriction of the prescribed P, not a separately chosen tower. -/
structure MarkedStratumPhaseFrame (M : MarkedIdeal n X) (H : Set X)
    (T : BlowupTower X Y) where
  B : CMfd.{u} n
  K : BlowupTower X B
  P : BlowupTower B Y
  tower_eq : T = K.append P
  testK : IsGeoTestTower M K
  historyK : IsOriginalBranchTestTower M H K
  emptyK : HasEmptyCausalBirthTails M H K
  q : ℕ
  cover : (geoTransformAlong M K).cosupp ⊆ oldCountLowOpen H K q
  testP : IsGeoTestTower (geoTransformAlong M K) P
  historyP : IsOriginalBranchTestTower (geoTransformAlong M K) (strictAlong K H) P
  high : CentresHaveOldCountAtLeast H K q P
  currentBound : ∀ y ∈ (geoTransformAlong M T).cosupp, oldCount H T y ≤ q
  attained : ∃ y ∈ (geoTransformAlong M T).cosupp, oldCount H T y = q
  canonicalQ : IsCanonical (phaseAuxiliary M H K q)
    ((CanonicalCentres.canonicalInvariant n).inv (phaseAuxiliary M H K q))
    (restrict (oldCountLowOpen H K q) P)

private theorem exists_highest_count (M : MarkedIdeal n X)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T)
    (hNe : (geoTransformAlong M T).cosupp.Nonempty) :
    ∃ q : ℕ, (∀ y ∈ (geoTransformAlong M T).cosupp, oldCount H T y ≤ q) ∧
      ∃ y ∈ (geoTransformAlong M T).cosupp, oldCount H T y = q := by
  let hc := (current_old_strata_eq_strict M h T hT hHistory).1
  let C := (geoTransformAlong M T).cosupp
  let B := (Finset.range (n + 1)).filter (fun q => ∃ y ∈ C, oldCount H T y = q)
  have hMem (y : Y) (hy : y ∈ C) : oldCount H T y ∈ B := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, y, hy, rfl⟩
    rw [oldCount_eq T (isNormalCrossingsCarrier_of_boundaryAdapted hc)]
    exact Nat.lt_succ_of_le (branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted hc) y)
  have hB : B.Nonempty := by
    obtain ⟨y, hy⟩ := hNe
    exact ⟨oldCount H T y, hMem y hy⟩
  let q := B.max' hB
  have hq := (Finset.mem_filter.mp (Finset.max'_mem B hB)).2
  exact ⟨q, fun y hy => Finset.le_max' B (oldCount H T y) (hMem y hy), hq⟩

private theorem fresh_frame_of_empty_state (M : MarkedIdeal n X)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T)
    (hEmpty : HasEmptyCausalBirthTails M H T)
    (hNe : (geoTransformAlong M T).cosupp.Nonempty) :
    Nonempty (MarkedStratumPhaseFrame M H T) := by
  obtain ⟨q, hBound, hAttained⟩ := exists_highest_count M h T hT hHistory hNe
  refine ⟨⟨Y, T, .refl, (BlowupTower.append_refl T).symm, hT, hHistory, hEmpty,
    q, hBound, trivial, ?_, trivial, hBound, hAttained, trivial⟩⟩
  intro U B _hSNC _hUnion
  trivial
private theorem whole_maximum_of_top_dictionary
    {B D Λ : Type*} [LinearOrder Λ]
    (C : Set B) (S : Set D) (g : D → B) (f : B → ℕ ×ₗ WithBot Λ) (v : D → Λ)
    (q : ℕ) (hCover : C ⊆ range g) (hSub : S ⊆ g ⁻¹' C) (hNe : S.Nonempty)
    (hBound : ∀ x ∈ C, (ofLex (f x)).1 ≤ q)
    (hOn : ∀ z ∈ S, f (g z) = toLex (q, (v z : WithBot Λ)))
    (hTop : ∀ z ∈ g ⁻¹' C, (ofLex (f (g z))).1 = q →
      f (g z) = toLex (q, if z ∈ S then (v z : WithBot Λ) else ⊥)) :
    ResolutionDriver.maxLocus f C = g '' ResolutionDriver.maxLocus v S := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := hCover hx.1
    have hzS : z ∈ S := by
      by_contra hzS
      obtain ⟨w, hw⟩ := hNe
      have hCmp := hx.2 (g w) (hSub hw)
      rw [hOn w hw] at hCmp
      have hzBound := hBound (g z) hx.1
      have hzTop : (ofLex (f (g z))).1 = q := by
        change toLex (q, (v w : WithBot Λ)) ≤ toLex (ofLex (f (g z))) at hCmp
        rw [Prod.Lex.toLex_le_toLex] at hCmp
        rcases hCmp with hLt | ⟨hEq, _hValue⟩
        · omega
        · exact hEq.symm
      have hzBot := hTop z hx.1 hzTop
      rw [if_neg hzS] at hzBot
      have hCmp' := hx.2 (g w) (hSub hw)
      rw [hOn w hw, hzBot] at hCmp'
      have hBad : (v w : WithBot Λ) ≤ ⊥ := by
        simpa only [Prod.Lex.toLex_le_toLex, lt_self_iff_false, eq_self_iff_true,
          false_or, true_and] using hCmp'
      exact (not_le_of_gt (WithBot.bot_lt_coe (v w))) hBad
    refine ⟨z, ⟨hzS, ?_⟩, rfl⟩
    intro w hw
    have hCmp := hx.2 (g w) (hSub hw)
    simpa only [hOn w hw, hOn z hzS, Prod.Lex.toLex_le_toLex,
      lt_self_iff_false, eq_self_iff_true, false_or, true_and, WithBot.coe_le_coe] using hCmp
  · rintro ⟨z, hz, rfl⟩
    refine ⟨hSub hz.1, ?_⟩
    intro y hy
    obtain ⟨w, rfl⟩ := hCover hy
    have hCount := hBound (g w) hy
    rw [hOn z hz.1]
    rcases hCount.lt_or_eq with hLow | hEqual
    · change toLex (ofLex (f (g w))) ≤ toLex (q, (v z : WithBot Λ))
      rw [Prod.Lex.toLex_le_toLex]
      exact Or.inl hLow
    · rw [hTop w hy hEqual, Prod.Lex.toLex_le_toLex]
      refine Or.inr ⟨rfl, ?_⟩
      split_ifs with hw
      · exact WithBot.coe_le_coe.mpr (hz.2 w hw)
      · exact bot_le



/-- The ENTIRE maximum of the DEFINED NEW value is the actual lower maximum
of its SAME internally produced literal phase. No desired max/cosupp premise. -/
theorem MarkedStratumPhaseFrame.whole_maximum (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (f : MarkedStratumPhaseFrame M H T) :
    ResolutionDriver.maxLocus (markedStratumHistoryValue M H T) (geoTransformAlong M T).cosupp =
      (Subtype.val : openPreimage f.P (oldCountLowOpen H f.K f.q) → Y) ''
        ResolutionDriver.maxLocus
          ((CanonicalCentres.canonicalInvariant n).inv (phaseAuxiliary M H f.K f.q)
            (restrict (oldCountLowOpen H f.K f.q) f.P))
          (geoTransformAlong (phaseAuxiliary M H f.K f.q)
            (restrict (oldCountLowOpen H f.K f.q) f.P)).cosupp := by
  rcases f with ⟨B, K, P, hT, hK, hHistoryK, hEmptyK, q, hCover,
    hP, hHistoryP, _hHigh, hBound, hAttained, hCan⟩
  subst T
  let V := oldCountLowOpen H K q
  let U := openPreimage P V
  let A := phaseAuxiliary M H K q
  let Q := restrict V P
  let R := CanonicalCentres.canonicalInvariant n
  let C := (geoTransformAlong M (K.append P)).cosupp
  let S := (geoTransformAlong A Q).cosupp
  let g : U → Y := Subtype.val
  have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hK
  have hA := (phaseAuxiliary_domain M hM h K hK hHistoryK q).1
  have hATest := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical R.isInvValue hA Q hCan
  have hCos : S = {p : U | p.val ∈ C ∧ oldCount H (K.append P) p.val = q} :=
    phase_whole_cosupp M hM h K hK hHistoryK q P hP hHistoryP hATest
  have hIn (y : Y) (hy : y ∈ C) : y ∈ U := by
    have hy' : y ∈ (geoTransformAlong (geoTransformAlong M K) P).cosupp := by
      simpa only [C, geoTransformAlong_append] using hy
    exact hCover (TransformOffCentre.cosupp_geoTransformAlong_subset (geoTransformAlong M K)
      hKD.isWellFormed.isClosedSubmanifold_N hKD.isWellFormed.isCoherent P hP hy')
  have hRange : C ⊆ range g := fun y hy => ⟨⟨y, hIn y hy⟩, rfl⟩
  have hSub : S ⊆ g ⁻¹' C := by
    intro p hp
    rw [hCos] at hp
    exact hp.1
  have hNe : S.Nonempty := by
    obtain ⟨y, hy, hq⟩ := hAttained
    let p : U := ⟨y, hIn y hy⟩
    refine ⟨p, ?_⟩
    rw [hCos]
    exact ⟨hy, hq⟩
  have hValue (p : U) (hp : p ∈ S) :
      markedStratumHistoryValue M H (K.append P) (g p) = toLex (q, (R.inv A Q p : WithBot (CanonicalCentres.ValTy n))) := by
    have hPoint := hp
    rw [hCos] at hPoint
    have hv := (phase_value_at_top M hM h K hK hHistoryK hEmptyK q hCover P hP hHistoryP
      hCan p hPoint.1 hPoint.2).2
    change markedStratumHistoryValue M H (K.append P) (g p) =
      toLex (q, if p ∈ S then (R.inv A Q p : WithBot (CanonicalCentres.ValTy n)) else ⊥) at hv
    simpa only [if_pos hp] using hv
  apply whole_maximum_of_top_dictionary C S g
    (markedStratumHistoryValue M H (K.append P)) (R.inv A Q) q hRange hSub hNe
  · intro y hy
    change oldCount H (K.append P) y ≤ q
    exact hBound y hy
  · exact hValue
  · intro p hp hq
    change oldCount H (K.append P) p.val = q at hq
    exact (phase_value_at_top M hM h K hK hHistoryK hEmptyK q hCover P hP hHistoryP
      hCan p hp hq).2

private theorem test_step_of_cosupport_cover (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (V : Opens X) (hCover : M.cosupp ⊆ V) (P : BlowupTower X Y)
    (hP : IsGeoTestTower M P) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (hCos : C ⊆ (geoTransformAlong M P).cosupp)
    (hLocal : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → X) M)
      (restrict V (.step P C π hπ))) : IsGeoTestTower M (.step P C π hπ) := by
  have hInside : C ⊆ (openPreimage P V : Set Y) := by
    intro y hy
    exact hCover (TransformOffCentre.cosupp_geoTransformAlong_subset M hN hI P hP (hCos hy))
  have hCentre := hLocal.2
  rw [geoTransformAlong_restrict V hN hI P hP] at hCentre
  have hNC := HironakaCompactOpenBlowupExtension.hasNormalCrossings_image_val hCentre.2.2
  have hImage : (Subtype.val : openPreimage P V → Y) ''
      ((Subtype.val : openPreimage P V → Y) ⁻¹' C) = C := by
    rw [image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hInside]
  rw [hImage] at hNC
  exact ⟨hP, hπ.1, hCos, hNC⟩


private theorem canonical_centre_has_phase_count
    (M : MarkedIdeal n X) (H : Set X) (T : BlowupTower X Y) (q : ℕ)
    (_hBound : ∀ y ∈ (geoTransformAlong M T).cosupp, oldCount H T y ≤ q)
    (hAttained : ∃ y ∈ (geoTransformAlong M T).cosupp, oldCount H T y = q)
    (C : Set Y)
    (hChoice : C = ∅ ∨ C = ResolutionDriver.maxLocus (markedStratumHistoryValue M H T)
      (geoTransformAlong M T).cosupp) :
    C ⊆ (geoTransformAlong M T).cosupp ∧ ∀ c ∈ C, q ≤ oldCount H T c := by
  rcases hChoice with rfl | hC
  · exact ⟨empty_subset _, fun _ hc => False.elim hc⟩
  rw [hC]
  refine ⟨fun _ hy => hy.1, ?_⟩
  intro c hc
  obtain ⟨x, hx, hqx⟩ := hAttained
  have hCmp := hc.2 x hx
  change toLex (oldCount H T x, _) ≤ toLex (oldCount H T c, _) at hCmp
  rw [Prod.Lex.toLex_le_toLex] at hCmp
  rcases hCmp with hLt | ⟨hEq, _hSecond⟩
  · omega
  · omega


private theorem empty_step_original_history (M : MarkedIdeal n X) {H : Set X}
    (T : BlowupTower X Y) (hHistory : IsOriginalBranchTestTower M H T)
    (π : Z → Y) (hπ : IsBlowupAlong n (∅ : Set Y) π) :
    IsOriginalBranchTestTower M H (.step T ∅ π hπ) := by
  intro U B hSNC hUnion
  have hOld := hHistory U B hSNC hUnion
  change IsGeoTestTower
    ({ MarkedIdeal.pullback (Subtype.val : U → X) M with
      E := B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E } : MarkedIdeal n U)
    (restrict U (.step T ∅ π hπ))
  apply (isGeoTestTower_step_iff _ _ _ _ _).mpr
  refine ⟨hOld, ?_⟩
  simpa only [preimage_empty] using MarkedIdeal.isAdmissibleCentre_empty
    (geoTransformAlong
      ({ MarkedIdeal.pullback (Subtype.val : U → X) M with
        E := B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E } : MarkedIdeal n U)
      (restrict U T))



private theorem joint_step_of_active_frame (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (f : MarkedStratumPhaseFrame M H T)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hChoice : C = ∅ ∨ C = ResolutionDriver.maxLocus (markedStratumHistoryValue M H T)
      (geoTransformAlong M T).cosupp) :
    IsGeoTestTower M (.step T C π hπ) ∧ IsOriginalBranchTestTower M H (.step T C π hπ) ∧
      ((geoTransformAlong M (.step T C π hπ)).cosupp = ∅ ∨
        Nonempty (MarkedStratumPhaseFrame M H (.step T C π hπ))) := by
  have hMax := MarkedStratumPhaseFrame.whole_maximum M hM h T f
  rcases f with ⟨B, K, P, hT, hK, hHistoryK, hEmptyK, q, hCover,
    hP, hHistoryP, hHigh, hBound, hAttained, hCan⟩
  subst T
  let V := oldCountLowOpen H K q
  let MC := geoTransformAlong M K
  let A := phaseAuxiliary M H K q
  let R := CanonicalCentres.canonicalInvariant n
  let U := openPreimage P V
  let Cq : Set U := (Subtype.val : U → Y) ⁻¹' C
  let Pnext := BlowupTower.step P C π hπ
  let Q := restrict V P
  let Qnext := restrict V Pnext
  have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hK
  have hA := (phaseAuxiliary_domain M hM h K hK hHistoryK q).1
  obtain ⟨hCos, hCentreHigh⟩ := canonical_centre_has_phase_count M H (K.append P) q
    hBound hAttained C hChoice
  have hCosMC : C ⊆ (geoTransformAlong MC P).cosupp := by
    simpa only [MC, geoTransformAlong_append] using hCos
  have hLocalChoice : Cq = ∅ ∨ Cq = ResolutionDriver.maxLocus (R.inv A Q)
      (geoTransformAlong A Q).cosupp := by
    by_cases hCEmpty : C = ∅
    · left
      simp only [Cq, hCEmpty, preimage_empty]
    · right
      have hCM : C = (Subtype.val : U → Y) ''
          ResolutionDriver.maxLocus (R.inv A Q) (geoTransformAlong A Q).cosupp :=
        (hChoice.resolve_left hCEmpty).trans hMax
      ext p
      constructor
      · intro hp
        have hpC : p.val ∈ C := hp
        rw [hCM] at hpC
        obtain ⟨z, hz, he⟩ := hpC
        exact (Subtype.ext he : z = p) ▸ hz
      · intro hp
        change p.val ∈ C
        rw [hCM]
        exact ⟨p, hp, rfl⟩
  have hCanNext : IsCanonical A (R.inv A) Qnext := by
    change IsCanonical A (R.inv A) Q ∧ _
    exact ⟨hCan, hLocalChoice⟩
  have hATestNext := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    R.isInvValue hA Qnext hCanNext
  obtain ⟨hLocalTest, hLocalHistory⟩ :=
    phase_local_test_history M hM h K hK hHistoryK q Pnext hATestNext
  have hPNext : IsGeoTestTower MC Pnext := test_step_of_cosupport_cover MC
    hKD.isWellFormed.isClosedSubmanifold_N hKD.isWellFormed.isCoherent
    V hCover P hP C π hπ hCosMC hLocalTest
  have hHistoryPNext : IsOriginalBranchTestTower MC (strictAlong K H) Pnext :=
    isOriginalBranchTestTower_of_restrict_cosupport_cover MC
      hKD.isWellFormed.isClosedSubmanifold_N hKD.isWellFormed.isCoherent
      V hCover Pnext hPNext hLocalHistory
  have hAll : IsGeoTestTower M (K.append Pnext) :=
    (isGeoTestTower_append_iff M K Pnext).mpr ⟨hK, hPNext⟩
  have hAllHistory : IsOriginalBranchTestTower M H (K.append Pnext) :=
    original_history_append_native M hM.isWellFormed K Pnext hK hHistoryK hHistoryPNext
  have hHighNext : CentresHaveOldCountAtLeast H K q Pnext := ⟨hHigh, hCentreHigh⟩
  have hTest := (isGeoTestTower_append_iff M K P).mpr ⟨hK, hP⟩
  have hNextBound : ∀ z ∈ (geoTransformAlong M (K.append Pnext)).cosupp,
      oldCount H (K.append Pnext) z ≤ q := by
    intro z hz
    have hTD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM (K.append P) hTest
    let Step : BlowupTower Y Z := .step .refl C π hπ
    have hStep : IsGeoTestTower (geoTransformAlong M (K.append P)) Step := ⟨trivial, hAll.2⟩
    have hzOld : π z ∈ (geoTransformAlong M (K.append P)).cosupp :=
      TransformOffCentre.cosupp_geoTransformAlong_subset (geoTransformAlong M (K.append P))
        hTD.isWellFormed.isClosedSubmanifold_N hTD.isWellFormed.isCoherent Step hStep hz
    exact (oldCount_step_le_native M hM.isWellFormed h (K.append P) C π hπ hAll hAllHistory z).trans
      (hBound (π z) hzOld)
  refine ⟨hAll, hAllHistory, ?_⟩
  by_cases hNextTop : ∃ z ∈ (geoTransformAlong M (K.append Pnext)).cosupp,
      oldCount H (K.append Pnext) z = q
  · exact Or.inr ⟨⟨B, K, Pnext, rfl, hK, hHistoryK, hEmptyK, q, hCover,
      hPNext, hHistoryPNext, hHighNext, hNextBound, hNextTop, hCanNext⟩⟩
  · by_cases hNe : (geoTransformAlong M (K.append Pnext)).cosupp.Nonempty
    · have hEmptyNext : HasEmptyCausalBirthTails M H (K.append Pnext) := by
        intro z hz
        have hLow : oldCount H (K.append Pnext) z < q := by
          have hb := hNextBound z hz
          have hn : oldCount H (K.append Pnext) z ≠ q := fun he => hNextTop ⟨z, hz, he⟩
          omega
        exact empty_birth_state_after_phase M hM h K hK hHistoryK hEmptyK q
          Pnext hPNext hHistoryPNext hHighNext z hz hLow
      exact Or.inr (fresh_frame_of_empty_state M h (K.append Pnext)
        hAll hAllHistory hEmptyNext hNe)
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hNe)

private theorem empty_tower_of_length_zero {B D : CMfd.{u} n}
    (S : BlowupTower B D) (hLen : S.length = 0) : IsEmptyTower S := by
  cases S with
  | refl => trivial
  | step S₀ C₀ π₀ hπ₀ =>
    simp only [BlowupTower.length_step, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false] at hLen

/-- The joint induction on the GIVEN actual canonical history. Compactness,
ordinary/history/phase certificates and any selected future are absent. -/
private theorem joint_history_of_isCanonical
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical M (markedStratumHistoryValue M H) T →
      IsGeoTestTower M T ∧ IsOriginalBranchTestTower M H T ∧
        ((geoTransformAlong M T).cosupp = ∅ ∨ Nonempty (MarkedStratumPhaseFrame M H T))
  | _, .refl, _hCan => by
    let T : BlowupTower X X := .refl
    have hTest : IsGeoTestTower M T := trivial
    have hHistory : IsOriginalBranchTestTower M H T := by
      intro U B _hSNC _hUnion
      trivial
    refine ⟨hTest, hHistory, ?_⟩
    by_cases hNe : (geoTransformAlong M T).cosupp.Nonempty
    · have hState : HasEmptyCausalBirthTails M H T := by
        intro x _hx
        let S := causalBirthTail H T x
        have hLen : S.length = 0 := by
          change (restrict (causalBirthOpen H T x)
            (tail T (T.length - birthYear H T x))).length = 0
          rw [length_restrict, length_tail]
          exact Nat.min_zero _
        exact empty_tower_of_length_zero S hLen
      exact Or.inr (fresh_frame_of_empty_state M h T hTest hHistory hState hNe)
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hNe)
  | _, .step T C π hπ, hCan => by
    obtain ⟨hTest, hHistory, hState⟩ := joint_history_of_isCanonical M hM h T hCan.1
    rcases hState with hClear | hFrame
    · have hC : C = ∅ := by
        rcases hCan.2 with hEmpty | hMax
        · exact hEmpty
        · apply eq_empty_iff_forall_notMem.mpr
          intro y hy
          have hyC := (hMax ▸ hy).1
          rw [hClear] at hyC
          exact hyC
      subst C
      have hStep : IsGeoTestTower M (.step T ∅ π hπ) :=
        (isGeoTestTower_step_iff M T ∅ π hπ).mpr
          ⟨hTest, MarkedIdeal.isAdmissibleCentre_empty _⟩
      have hHistoryStep := empty_step_original_history M T hHistory π hπ
      refine ⟨hStep, hHistoryStep, Or.inl ?_⟩
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hTI := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
        (𝔪 := M) hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hTest
      let Step : BlowupTower _ _ := .step .refl ∅ π hπ
      have hStepLocal : IsGeoTestTower (geoTransformAlong M T) Step := ⟨trivial, hStep.2⟩
      have hzOld := TransformOffCentre.cosupp_geoTransformAlong_subset (geoTransformAlong M T)
        hTI.1 hTI.2 Step hStepLocal hz
      rw [hClear] at hzOld
      exact hzOld
    · obtain ⟨f⟩ := hFrame
      exact joint_step_of_active_frame M hM h T f C π hπ hCan.2



private theorem birth_membership_of_coe_value (M : MarkedIdeal n X) (H : Set X)
    (T : BlowupTower X Y) (y : Y) (v : CanonicalCentres.ValTy n)
    (hv : markedStratumHistoryValue M H T y = toLex (oldCount H T y,
      (v : WithBot (CanonicalCentres.ValTy n)))) :
    causalBirthPoint H T y ∈
      (geoTransformAlong (markedStratumBirth M H T y) (causalBirthTail H T y)).cosupp := by
  by_contra hn
  have hh := congrArg (fun l : ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) => (ofLex l).2) hv
  have hBad : (⊥ : WithBot (CanonicalCentres.ValTy n)) = v := by
    change (if causalBirthPoint H T y ∈
        (geoTransformAlong (markedStratumBirth M H T y) (causalBirthTail H T y)).cosupp then
      ((CanonicalCentres.canonicalInvariant n).inv (markedStratumBirth M H T y)
        (causalBirthTail H T y) (causalBirthPoint H T y) : WithBot (CanonicalCentres.ValTy n))
      else ⊥) = (v : WithBot (CanonicalCentres.ValTy n)) at hh
    simpa only [if_neg hn] using hh
  exact WithBot.coe_ne_bot hBad.symm

private theorem birth_data_of_active_frame (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (f : MarkedStratumPhaseFrame M H T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) :
    IsInvDomain n (markedStratumBirth M H T y) ∧
      IsCanonical (markedStratumBirth M H T y)
        ((CanonicalCentres.canonicalInvariant n).inv (markedStratumBirth M H T y))
        (causalBirthTail H T y) ∧
      causalBirthPoint H T y ∈
        (geoTransformAlong (markedStratumBirth M H T y) (causalBirthTail H T y)).cosupp := by
  rcases f with ⟨B, K, P, hT, hK, hHistoryK, hEmptyK, q, hCover,
    hP, hHistoryP, hHigh, hBound, _hAttained, hCan⟩
  subst T
  have hTest := (isGeoTestTower_append_iff M K P).mpr ⟨hK, hP⟩
  have hHistory := original_history_append_native M hM.isWellFormed K P hK hHistoryK hHistoryP
  have hBirthDomain := (markedStratumBirth_domain M hM h (K.append P) hTest hHistory y).1
  refine ⟨hBirthDomain, ?_, ?_⟩
  · by_cases hLow : oldCount H (K.append P) y < q
    · have he := empty_birth_state_after_phase M hM h K hK hHistoryK hEmptyK q
        P hP hHistoryP hHigh y hy hLow
      exact ResolutionInvariantExt.isCanonical_of_isEmptyTower _ _ _ he
    · have hTop : oldCount H (K.append P) y = q := by
        have hb := hBound y hy
        omega
      have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hK
      have hy' : y ∈ (geoTransformAlong (geoTransformAlong M K) P).cosupp := by
        simpa only [geoTransformAlong_append] using hy
      have hx := TransformOffCentre.cosupp_geoTransformAlong_subset (geoTransformAlong M K)
        hKD.isWellFormed.isClosedSubmanifold_N hKD.isWellFormed.isCoherent P hP hy'
      let p : openPreimage P (oldCountLowOpen H K q) := ⟨y, hCover hx⟩
      exact (phase_value_at_top M hM h K hK hHistoryK hEmptyK q hCover P hP hHistoryP hCan p hy hTop).1
  · by_cases hLow : oldCount H (K.append P) y < q
    · have he := empty_birth_state_after_phase M hM h K hK hHistoryK hEmptyK q
        P hP hHistoryP hHigh y hy hLow
      exact empty_birth_membership M hM h (K.append P) hTest hHistory y hy he
    · have hTop : oldCount H (K.append P) y = q := by
        have hb := hBound y hy
        omega
      have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hK
      have hy' : y ∈ (geoTransformAlong (geoTransformAlong M K) P).cosupp := by
        simpa only [geoTransformAlong_append] using hy
      have hx := TransformOffCentre.cosupp_geoTransformAlong_subset (geoTransformAlong M K)
        hKD.isWellFormed.isClosedSubmanifold_N hKD.isWellFormed.isCoherent P hP hy'
      let p : openPreimage P (oldCountLowOpen H K q) := ⟨y, hCover hx⟩
      let A := phaseAuxiliary M H K q
      let Q := restrict (oldCountLowOpen H K q) P
      let R := CanonicalCentres.canonicalInvariant n
      have hA := (phaseAuxiliary_domain M hM h K hK hHistoryK q).1
      have hATest := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical R.isInvValue hA Q hCan
      have hCos := phase_whole_cosupp M hM h K hK hHistoryK q P hP hHistoryP hATest
      have hp : p ∈ (geoTransformAlong A Q).cosupp := by
        rw [hCos]
        exact ⟨hy, hTop⟩
      have hv := (phase_value_at_top M hM h K hK hHistoryK hEmptyK q hCover
        P hP hHistoryP hCan p hy hTop).2
      rw [if_pos hp] at hv
      apply birth_membership_of_coe_value M H (K.append P) y (R.inv A Q p)
      simpa only [hTop] using hv

/-- ANY tower canonical for the DEFINED NEW proper-carrier Psi internally
has native ordinary testness, EVERY original local branch test history,
SAME actual birth domains/canonical tails/cosupport membership, and a
common literal phase whenever current native cosupport is nonempty.
No future test/history/CAN/phase/cosupport certificate is a caller input. -/
theorem markedStratum_canonical_history_joint_interpretation
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y)
    (hCan : IsCanonical M (markedStratumHistoryValue M H) T) :
    IsGeoTestTower M T ∧ IsOriginalBranchTestTower M H T ∧
      (∀ y ∈ (geoTransformAlong M T).cosupp,
        IsInvDomain n (markedStratumBirth M H T y) ∧
          IsCanonical (markedStratumBirth M H T y)
            ((CanonicalCentres.canonicalInvariant n).inv (markedStratumBirth M H T y))
            (causalBirthTail H T y) ∧
          causalBirthPoint H T y ∈
            (geoTransformAlong (markedStratumBirth M H T y) (causalBirthTail H T y)).cosupp) ∧
      ((geoTransformAlong M T).cosupp.Nonempty → Nonempty (MarkedStratumPhaseFrame M H T)) := by
  obtain ⟨hTest, hHistory, hState⟩ := joint_history_of_isCanonical M hM h T hCan
  refine ⟨hTest, hHistory, ?_, ?_⟩
  · intro y hy
    rcases hState with hClear | hFrame
    · rw [hClear] at hy
      exact False.elim hy
    · obtain ⟨f⟩ := hFrame
      exact birth_data_of_active_frame M hM h T f y hy
  · intro hNe
    rcases hState with hClear | hFrame
    · exact False.elim ((Set.not_nonempty_iff_eq_empty.mpr hClear) hNe)
    · exact hFrame

end
end Hironaka.HironakaOriginalNCMarkedStratumCanonicalHistory
