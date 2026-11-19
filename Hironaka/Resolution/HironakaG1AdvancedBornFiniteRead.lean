import Hironaka.Resolution.HironakaG1LocalizedLaterBornRead

/-! The original finite positive read at the actual advanced run head. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace Classical
open scoped Topology

namespace Hironaka.HironakaG1AdvancedBornFiniteRead

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain
  InvDomainMemberRestriction InvDomainRebase HomogenizedIdealAlong CoefficientIdealRestriction
  HironakaG1RecursiveMemberValueTransport HironakaG3RRawRegimeLocality RelativePrincipalizationSpan

/-- For an ordered SNC list only the incident members of the old prefix are
deleted. The new suffix survives literally and in its original order, even
if some missing members coincide as sets. -/
theorem retained_boundary_eq_old_filter_append_new {n : ℕ} {X : CMfd.{0} n}
    (E₀ E₁ : List (Set X)) (hE : NormalCrossings.IsSNCDivisor n (E₀ ++ E₁)) (p : X) :
    (E₀ ++ E₁).filter (fun F => decide ¬ (F ∈ E₀ ∧ p ∈ F)) =
      E₀.filter (fun F => decide (p ∉ F)) ++ E₁ := by
  rw [List.filter_append]
  congr 1
  · apply List.filter_congr
    intro F hF
    simp [hF]
  · apply List.filter_eq_self.mpr
    intro F hF
    apply decide_eq_true
    rintro ⟨hF₀, hpF⟩
    obtain ⟨i, hi⟩ := List.get_of_mem hF₀
    obtain ⟨j, hj⟩ := List.get_of_mem hF
    let i' : Fin (E₀ ++ E₁).length := ⟨i, by simp only [List.length_append]; omega⟩
    let j' : Fin (E₀ ++ E₁).length := ⟨E₀.length + j, by
      simp only [List.length_append]; omega⟩
    have hi' : (E₀ ++ E₁).get i' = F := by
      rw [List.get_eq_getElem, List.getElem_append_left (show i'.val < E₀.length from i.isLt)]
      exact hi
    have hj' : (E₀ ++ E₁).get j' = F := by
      rw [List.get_eq_getElem, List.getElem_append_right (show E₀.length ≤ j'.val from Nat.le_add_right _ _)]
      simpa only [List.get_eq_getElem, j', Nat.add_sub_cancel_left] using hj
    have hij := SimultaneousNormalCrossings.eq_of_eventually_mem_iff hE
      (hi'.symm ▸ hpF) (hj'.symm ▸ hpF) (Eventually.of_forall fun x => by rw [hi', hj'])
    have hv := congrArg Fin.val hij
    change i.val = E₀.length + j.val at hv
    omega

set_option maxHeartbeats 1300000 in
/-- Read a genuine canonical suffix at its own positive run head. The
member selection uses the transformed original bar and the retained
original prefix of its ordered boundary at that head. -/
theorem advanced_positive_stepOne_finite_read {n k b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J : MarkedIdeal n X) (hJ : IsInvDomain (k + 1) J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) T)
    (y : Y) (hy : y ∈ (geoTransformAlong J T).cosupp)
    (hl : level J T y = b + 1) (hNS : ¬ IsSpecial J T y) :
    let r := regimeRun (stepRegime J (b + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA J H p
    let B := geoTransformAlong (barMarked J) H
    stepRegime J (b + 1) H p ∧ p ∈ B.cosupp ∧ p ∈ O ∧
    ∀ (W : Opens (split T r).1), W ≤ O → ∀ hpW : p ∈ W,
      let K := positiveMemberOn J H p W
      let V := BlowupTowerTransforms.restrict W S
      let z : openPreimage S W := ⟨y, hpW⟩
      IsInvDomain k K ∧ IsCanonical K ((invFamily hn k).inv K) V ∧
      z ∈ (geoTransformAlong K V).cosupp ∧
      K.E = (((origMembers J H).filter (fun F => decide (p ∉ F))) ++ B.E.drop J.E.length).map
        ((Subtype.val : W → (split T r).1) ⁻¹' ·) ∧
      K.d = (coeffMarkedAlong B).d ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J T y =
        toLex (b + 1, ((invFamily hn k).inv K V z : WithTop (ValTy k))) := by
  intro r H S p O B
  let R := invFamily hn k
  let K₀ := memberRestrict B (membersThrough B.E (origMembers J H) p)
  obtain ⟨hBT, _, hCos⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical R J hJ hMax hn T hCan
  have hyB := hCos.symm ▸ hy
  have hBC := (Seq.StepOneBridge.isCanonical_iff R J hJ hMax hn T).mp hCan
  have hLower := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical (k := k + 1) J R
    hJ.isWellFormed hJ.one_le_d hn hMax hJ.dimLE T hBT hBC y hyB hNS
  rw [hl] at hLower
  have hStage := stepRegime_and_mem_cosupp_head J hJ.isWellFormed T hBT hyB hNS
  rw [hl] at hStage
  obtain ⟨hp, hDom, hLowerCan, hz⟩ := hLower
  refine ⟨hStage.1, hStage.2, hp, ?_⟩
  intro W hW hpW K V z
  have hHeadTest : IsGeoTestTower (barMarked J) H :=
    ((isGeoTestTower_iff_head_tail (barMarked J) T r).mp hBT).1
  have hB : B.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked J hJ.isWellFormed) H hHeadTest
  have hK₀ : K₀.IsWellFormed := isWellFormed_memberRestrict hn hB _
  have hDomO : IsInvDomain k (positiveMemberOn J H p O) := hDom
  have hCanO : IsCanonical (positiveMemberOn J H p O) (R.inv (positiveMemberOn J H p O))
      (BlowupTowerTransforms.restrict O S) := hLowerCan
  obtain ⟨hKW, hCanW, hVal⟩ :=
    Seq.MaxLocusLocal.restrict_nestedOpens R hK₀.isCoherent hW hDomO S hCanO
  have hHol : ∀ x f, K₀.ideal.mem x f → HolomorphicAt n f x :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hK₀.isCoherent hf
  have hzO : (⟨y, hp⟩ : openPreimage S O) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → (split T r).1) K₀)
        (BlowupTowerTransforms.restrict O S)).cosupp := hz
  rw [cosupp_restrict_raw K₀ hHol O S] at hzO
  have hzW : z ∈ (geoTransformAlong K V).cosupp := by
    change z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → (split T r).1) K₀)
      (BlowupTowerTransforms.restrict W S)).cosupp
    rw [cosupp_restrict_raw K₀ hHol W S]
    exact hzO
  have hE : K.E = (B.E.filter (fun F => decide ¬ (F ∈ origMembers J H ∧ p ∈ F))).map
      ((Subtype.val : W → (split T r).1) ⁻¹' ·) := by
    change K₀.E.map _ = _
    rw [memberRestrict_membersThrough_E]
  have hSplitE : origMembers J H ++ B.E.drop J.E.length = B.E := List.take_append_drop _ _
  have hSNC : NormalCrossings.IsSNCDivisor n (origMembers J H ++ B.E.drop J.E.length) :=
    hSplitE.symm ▸ hB.isSNCDivisor
  have hChron := retained_boundary_eq_old_filter_append_new (origMembers J H)
    (B.E.drop J.E.length) hSNC p
  rw [hSplitE] at hChron
  rw [hChron] at hE
  refine ⟨hKW, hCanW, hzW, hE, rfl, ?_⟩
  have hRead := Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R J (lowerMarkedM J) T hNS
  rw [hl, Seq.StepOneValueMasked.lowerValueL_eq_of_mem R J (lowerMarkedM J) hp] at hRead
  exact hRead.trans (congrArg (fun v : ValTy k => toLex (b + 1, (v : WithTop (ValTy k))))
    (hVal z hzW).symm)

end Hironaka.HironakaG1AdvancedBornFiniteRead
