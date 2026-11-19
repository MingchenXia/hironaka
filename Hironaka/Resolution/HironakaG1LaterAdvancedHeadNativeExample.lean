import Hironaka.Resolution.HironakaG1LaterAdvancedHeadNumericalExample
import Hironaka.Resolution.HironakaG1PositiveNormalChronology
import Hironaka.Resolution.HironakaG1NormalUnequalDepth
import Hironaka.Resolution.HironakaSharpActualCurveExceptionalPointExponent
import Hironaka.Resolution.HironakaG8GenericFullMonomial
import Hironaka.Resolution.HironakaG1ProperNormalPhaseNative
import Hironaka.Resolution.HironakaActualNativeSectionStepOneHistory
import Hironaka.Resolution.HironakaG1SupportedStepOne
import Hironaka.Resolution.HironakaG1LaterPositiveSuccessorRead
import Hironaka.Resolution.HironakaG1LaterSelectedActualOrder

/-! The literal native lift of the canonical advanced-head example. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterAdvancedHeadNativeExample

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres StepOneValue StepOneValueMasked StepOneRegime
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaRelativeNormalIdeal
  HironakaG1PositiveNormalJointExample HironakaG1PositiveNormalNonspecialExample
  HironakaG1LaterPositiveNormalExample HironakaG1LaterAdvancedHeadExample
  HironakaG1LaterPositiveSuccessorRead GermIdealPullbackCalculus
  RelativePrincipalizationSpan GermIdealOrder InvertibleIdealQuotient
  NormalCrossings HironakaPrincipalizationBoundary HironakaG1PositiveNormalPhase
  HironakaG1LaterSelectedActualOrder NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  GeneralValue MarkedIdealRestrictOpen MarkedIdealBiholomorphism CompanionRebase
  HomogenizedIdealAlong CoefficientIdeal InvDomainMemberRestriction InvDomainTowerAlong
  HironakaG1InitialPositiveGeneralRead CompanionReductionAlong BoundaryCount
  HironakaG1LaterAdvancedHeadCanonicalExample HironakaG1LaterAdvancedHeadNumericalExample
  HironakaG1ProperNormalPhaseNative HironakaG1ProperCarrierNormalLocalClass
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionRegularity
  HironakaActualNativeSectionStepOneHistory HironakaActualSectionBoundaryGeometry
  HironakaG8GenericFullMonomial HironakaSharpActualCurveExceptionalPointExponent
  PositiveDimensionalComponent
  StepOneLowerDomain NonmonomialOrderZero GermIdealOrder
  HironakaActualNativeSectionOrderHistory HironakaActualNativeSectionNormalCrossings
  HironakaActualNativeInvariantDomain HironakaG8HomStable InvDomainTowerAlong InvDomainRebase
  HironakaG8MemberLoci HironakaG1SupportedStepOne Hironaka.HolomorphicIdealSheaves
  BlowupFlatCoordinates BlowupMonomialCharts BlowupStrictSubmanifold
  HironakaRelativeNormalIdeal HironakaG8MixedOrderInvariance BlowupTowerSplit
  HironakaG1PositiveNormalChronology HironakaG1NormalUnequalDepth
  HironakaSmoothSubmersionCanonicalValueDimensionShift

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev C : Set X := {p}
private abbrev D (i : Fin 3) : Set X := {z | z.val i = 0}
private abbrev P : MarkedIdeal 3 X := properNormalMarked sourceRecord
private abbrev M : MarkedIdeal 3 X := {P with E := [D 0, D 1]}
private abbrev T : BlowupTower X X := .refl
private abbrev O := maskA M B q
private abbrev L := lowerMarkedM M 1 B q

private abbrev Dsrc (i : Fin 2) : Set U := {z | z.val i = 0}
private abbrev Q : MarkedIdeal 2 U := {sourceRecord with E := [Dsrc 0, Dsrc 1]}

private theorem source_snc : IsSNCDivisor 2 Q.E := by
  classical
  refine ⟨?_, ?_⟩
  · intro H hH
    change H ∈ [Dsrc 0, Dsrc 1] at hH
    rcases List.mem_cons.mp hH with rfl | hH
    · exact isClosed_eq ((EuclideanSpace.proj (𝕜 := ℂ) _).continuous.comp
        continuous_subtype_val) continuous_const
    rw [List.mem_singleton] at hH
    subst H
    exact isClosed_eq ((EuclideanSpace.proj (𝕜 := ℂ) _).continuous.comp
      continuous_subtype_val) continuous_const
  · intro x
    let idx : Fin Q.E.length → Fin 2 := fun i => ⟨i.val, i.isLt⟩
    have hGet (i : Fin Q.E.length) : Q.E.get i = Dsrc (idx i) := by fin_cases i <;> rfl
    have hChart (z : U) : (complexChartAt (n := 2) x).val z = z.val := rfl
    refine ⟨fun i => {idx i}, ?_, fun _ _ => Finset.card_singleton _, ?_⟩
    · let Φ : LocalHolomorphicEquivAt (n := 2) ((complexChartAt (n := 2) x).val x) :=
        { source := univ
          target := univ
          isOpen_source := isOpen_univ
          isOpen_target := isOpen_univ
          center_mem_source := mem_univ _
          toFun := fun w => w - x.val
          invFun := fun w => w + x.val
          toFun_holomorphic := (differentiable_id.sub_const x.val).differentiableOn
          invFun_holomorphic := (differentiable_id.add_const x.val).differentiableOn
          mapsTo_toFun := mapsTo_univ _ _
          mapsTo_invFun := mapsTo_univ _ _
          left_inv := fun w _ => sub_add_cancel w x.val
          right_inv := fun w _ => add_sub_cancel_right w x.val }
      refine ⟨Φ, ?_, by change _ - _ = 0; rw [hChart, sub_self], ?_⟩
      · intro w _
        let y : U := ⟨w, mem_univ _⟩
        change w ∈ (chartAt (ComplexModel 2) x).target
        rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
        exact (OpenPartialHomeomorph.refl (ComplexModel 2)).map_subtype_source
          ⟨x⟩ (x := y) (mem_univ _)
      · intro i hi y _ _
        change x ∈ Q.E.get i at hi
        change y ∈ Q.E.get i ↔ _
        rw [hGet] at hi ⊢
        have hi0 : x.val (idx i) = 0 := hi
        change y.val (idx i) = 0 ↔
          (complexChartAt (n := 2) x).val y - x.val ∈ coordSubspace {idx i}
        rw [hChart]
        simp [coordSubspace, hi0]
    · intro i _ j _ hij
      exact Fin.ext (congrArg (fun j : Fin 2 => j.val) (Finset.singleton_injective hij))

/-- The native source with both original coordinate axes lies in the invariant domain. -/
theorem Q_domain : IsInvDomain 2 Q :=
  HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor
    sourceRecord_domain.isWellFormed.isCoherent
    (fun x => sourceRecord_domain.isNonzeroAlongAt x (mem_univ _)) source_snc


private theorem plane_closed : IsClosed (zeroPlane U) :=
  (liftedCarrier_closed_submanifold
    (HomogenizedGlueingTower.isClosedSubmanifold_univ (n := 2) (M := U))).1

private abbrev Sec : MarkedIdeal 3 X := sectionMarked Q

private theorem native_curve_born_zero {A : CMfd.{0} 2} (K : MarkedIdeal 2 A)
    (hK : IsInvDomain 1 K) {z : A} (hz : z ∈ K.cosupp) (i : Fin K.E.length)
    (hi : z ∈ K.E.get i) : nmOrd K z = 0 := by
  obtain ⟨j, hj, hr⟩ := hK.dimLE z hz.1
  have hj1 : j = 1 := by
    by_contra h
    have hj0 : j = 0 := by omega
    rw [hj0] at hr
    obtain ⟨U, hU, hzU, hIso⟩ := exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hr
    obtain ⟨g, hg, hFreq⟩ := hK.isNonzeroAlongAt z hz.1
    obtain ⟨x, ⟨hxN, hxg⟩, hxU⟩ := (hFreq.and_eventually (hU.mem_nhds hzU)).exists
    have he : x = z := hIso ⟨hxN, hxU⟩
    rw [he] at hxg
    have hHol := GermIdeal.IsCoherent.holomorphicAt_mem hK.isWellFormed.isCoherent hg
    exact hxg ((vanishesToOrderOn_one_iff hz.1 hHol).mp ((hz.2 g hg).mono hK.one_le_d))
  rw [hj1] at hr
  have hExp := actual_curve_member_divExp_eq_ordinaryTraceOrder (by decide : 0 < 2)
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isSNCDivisor hK.isWellFormed.isTransverse
    hK.isWellFormed.isCoherent hK.isNonzeroAlongAt hr i hi
  exact full_nmOrd_zero_of_order_eq_member (by decide) K hK i hz.1 hi hExp.symm

private abbrev D' (i : Fin 3) := geoStrictTransform π C (D i)
private abbrev F : Set Y := π ⁻¹' C
private abbrev Z := nativeManifold (Y := X) (Nat.le_succ 2) (zeroPlane U) (zeroPlane_regular U)
private abbrev N₀ := nativePullback (Y := X) (Nat.le_succ 2) (zeroPlane U) (zeroPlane_regular U) Sec
private abbrev R := invFamily (by decide : 0 < 2) 1

private theorem q_proj : π q = p := joint_first_point_blowup_positive_normal_contact.2.2.2.1
private theorem q_D : q ∈ D' 0 := joint_first_point_blowup_positive_normal_contact.2.2.2.2.2.1
private theorem q_F : q ∈ F := by
  change π q ∈ C
  rw [q_proj]
  exact mem_singleton _
private theorem q_not_D1 : q ∉ D' 1 := by
  have h := joint_added_boundary_upper_regime_advances.2.1
  change BoundaryCount.boundaryCount [D' 0, D' 1] q = 1 at h
  intro hh
  classical
  unfold BoundaryCount.boundaryCount at h
  rw [Finset.filter_true_of_mem] at h
  · simp at h
  · intro i _
    fin_cases i
    · exact q_D
    · exact hh

private theorem strict_section_born_ne {V : Set Y}
    (hV : V = HomogenizedGlueingTower.strictAlong B (zeroPlane U)) :
    (Subtype.val : V → Y) ⁻¹' F ≠ (Subtype.val : V → Y) ⁻¹' D' 0 := by
  intro hEq
  let v := EuclideanSpace.single (1 : Fin 3) (1 : ℂ)
  let w := yChart.invFun v
  have hw : w ∈ yChart.source := yChart.toPartialEquiv.map_target (chart_all v)
  have hc : yChart.toFun w = v := yChart.toPartialEquiv.right_inv (chart_all v)
  have hproj : (π w).val = monomial 0 (1 : Fin 3) v := by rw [chart_projection w hw, hc]
  have hD : π w ∈ D 0 := by
    change (π w).val (0 : Fin 3) = 0
    rw [hproj, monomial_apply]
    simp [v]
  have hp0 : p.val = 0 := map_zero (tangentInclusion 2 1)
  have hOff : π w ∉ C := by
    intro hp
    have h := congrArg (fun x : X => x.val (1 : Fin 3)) (mem_singleton_iff.mp hp)
    change (π w).val (1 : Fin 3) = p.val (1 : Fin 3) at h
    rw [hproj, hp0, monomial_apply] at h
    simp [v] at h
  have hSec : π w ∈ zeroPlane U := by
    refine ⟨mem_univ _, ?_⟩
    ext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    rw [hj]
    change (π w).val (2 : Fin 3) = 0
    rw [hproj, monomial_apply]
    simp [v]
  have hwV : w ∈ V := by
    rw [hV]
    change w ∈ geoStrictTransform π C (zeroPlane U)
    exact subset_closure (show π w ∈ zeroPlane U \ C from ⟨hSec, hOff⟩)
  have hwD : (⟨w, hwV⟩ : V) ∈ (Subtype.val : V → Y) ⁻¹' D' 0 :=
    subset_closure (show π w ∈ D 0 \ C from ⟨hD, hOff⟩)
  exact hOff ((hEq.symm ▸ hwD : (⟨w, hwV⟩ : V) ∈ (Subtype.val : V → Y) ⁻¹' F))

set_option maxHeartbeats 850000 in
set_option backward.isDefEq.respectTransparency false in
private theorem native_read {A Z' : CMfd.{0} 2} (I : MarkedIdeal 2 A)
    (hI : IsInvDomain 2 I) (H : BlowupTower A Z') (hH : IsGeoTestTower (barMarked I) H)
    (x : Z') (hx : x ∈ (geoTransformAlong (barMarked I) H).cosupp)
    (hl : level I H x = 1) (hr : regimeRun (stepRegime I 1) H x = 0)
    (D₀ D₁ F₀ : Set Z') (hE : (geoTransformAlong (barMarked I) H).E = [D₀, D₁, F₀])
    (ho : origMembers I H = [D₀, D₁])
    (hxD : x ∈ D₀) (hxD' : x ∉ D₁) (hxF : x ∈ F₀)
    (hneD : F₀ ≠ D₀) (hneD' : F₀ ≠ D₁) :
    Seq.StepOneValueMasked.stepOneInvM R I H x = toLex (1, (⊤ : WithTop (ValTy 1))) ∨
      ∃ v : ValTy 1, fstEntry v = 0 ∧
        Seq.StepOneValueMasked.stepOneInvM R I H x = toLex (1, (v : WithTop (ValTy 1))) := by
  by_cases hSp : IsSpecial I H x
  · left
    rw [Seq.StepOneValueMasked.stepOneInvM,
      Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R I (lowerMarkedM I) H hSp, hl]
  right
  let G := geoTransformAlong (barMarked I) H
  let K := memberRestrict G (membersThrough G.E (origMembers I H) x)
  let O := maskA I H x
  let J := lowerMarkedM I 1 H x
  let S := CMfd.of (n := 2) O
  let T : BlowupTower S S := .refl
  have hJ : IsInvDomain 1 J := isInvDomain_lowerMarked_succ I hI.isWellFormed hI.one_le_d
    (by decide) H hH hI.dimLE hl
  have hxO : x ∈ O := mem_maskA I hI.isWellFormed hI.one_le_d (by decide) H hH hl.ge hSp
  let z : O := ⟨x, hxO⟩
  have hG : G.IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (isWellFormed_barMarked I hI.isWellFormed) H hH
  have hK := isWellFormed_memberRestrict (by decide : 0 < 2) hG
    (membersThrough G.E (origMembers I H) x)
  have hz : z ∈ J.cosupp := by
    change z ∈ (MarkedIdeal.pullback (Subtype.val : O → Z') K).cosupp
    rw [cosupp_pullback_val K (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hK.isCoherent hg) O]
    change x ∈ K.cosupp
    have hdG : 1 ≤ G.d := by
      change 1 ≤ (geoTransformAlong (barMarked I) H).d
      rw [d_geoTransformAlong]
      exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
    rw [cosupp_memberRestrict hG hdG]
    exact ⟨hx, fun _ hi => (mem_membersThrough.mp hi).2⟩
  have hKE : K.E = [D₁, F₀] := by
    classical
    change (memberRestrict G (membersThrough G.E (origMembers I H) x)).E = _
    rw [memberRestrict_membersThrough_E, show G.E = [D₀,D₁,F₀] from hE, ho]
    simp [hxD, hxD', hneD, hneD']
  have hJEt : J.E = [(Subtype.val : O → Z') ⁻¹' D₁, (Subtype.val : O → Z') ⁻¹' F₀] := by
    change K.E.map ((Subtype.val : O → Z') ⁻¹' ·) = _
    rw [hKE]
    rfl
  have hm : (Subtype.val : O → Z') ⁻¹' F₀ ∈ J.E := by rw [hJEt]; simp
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
  have hi' : z ∈ J.E.get i := by
    rw [hi]
    exact hxF
  let v := R.inv J T z
  have hv : fstEntry v = 0 := by
    have h := native_curve_born_zero (A := S) J hJ hz i hi'
    change (ofLex (genInv _ J T z)).1 = 0
    rw [genInv_fst]
    exact h
  refine ⟨v, hv, ?_⟩
  change Seq.StepOneValueMasked.stepOneInvL R I (lowerMarkedM I) H x = _
  rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R I (lowerMarkedM I) H hSp, hl, hr]
  have hSplit : split H 0 = ⟨Z', H, BlowupTower.refl (X := Z')⟩ := by cases H <;> rfl
  simp only [head, tail]
  erw [hSplit]
  change toLex (1, Seq.StepOneValueMasked.lowerValueL R I (lowerMarkedM I) 1 H
    (BlowupTower.refl (X := Z')) x) = _
  unfold Seq.StepOneValueMasked.lowerValueL
  erw [dif_pos (show (BlowupTower.refl (X := Z')).proj x ∈
    lowerMask I 1 H ((BlowupTower.refl (X := Z')).proj x) from hxO)]
  rfl

private theorem canonical_length_one {n : ℕ} {A Z' : CMfd.{0} n}
    (I : MarkedIdeal n A) {Λ : Type} [LinearOrder Λ]
    (f : ∀ {Y : CMfd.{0} n}, BlowupTower A Y → Y → Λ)
    (H : BlowupTower A Z') (hl : H.length = 1) (hTest : IsGeoTestTower I H)
    (hs : I.cosupp.Subsingleton) : IsCanonical I f H := by
  cases H with
  | refl => trivial
  | step T C π hπ =>
    have hLen : T.length = 0 := Nat.succ.inj hl
    cases T with
    | refl =>
      refine ⟨trivial, ?_⟩
      have hSub : C ⊆ I.cosupp := hTest.2.2.1
      by_cases hC : C.Nonempty
      · right
        obtain ⟨x, hx⟩ := hC
        ext y
        refine ⟨fun hy => ⟨hSub hy, fun z hz => ?_⟩, fun hy => ?_⟩
        · rw [hs hz (hSub hy)]
        · have he : y = x := hs hy.1 (hSub hx)
          exact he.symm ▸ hx
      · exact Or.inl (not_nonempty_iff_eq_empty.mp hC)
    | step => exact (Nat.succ_ne_zero _ hLen).elim

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
/-- On the genuine lifted history the native lower branch is monomial
whenever it is finite. The padded value has finite lower order one. No
order-preserving dimension shift can identify the original values. -/
theorem joint_advanced_head_literal_native_discrepancy :
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ x ∈ V, RegularAtDim (n := 3) V x 2)
      (N : BlowupTower Z (nativeManifold (Nat.le_succ 2) V hV))
      (z : nativeManifold (Nat.le_succ 2) V hV),
      Lift (Nat.le_succ 2) (zeroPlane U) (plane_closed) (zeroPlane_regular U)
        Sec.E B V hVc hV N ∧
      N.length = 1 ∧ z.val = q ∧ z ∈ (geoTransformAlong N₀ N).cosupp ∧
      IsCanonical N₀ (Seq.StepOneValueMasked.stepOneInvM R N₀) N ∧
      let v := Seq.StepOneValueMasked.stepOneInvM R N₀ N z
      (v = toLex (1, (⊤ : WithTop (ValTy 1))) ∨
        ∃ w : ValTy 1, fstEntry w = 0 ∧ v = toLex (1, (w : WithTop (ValTy 1)))) := by
  have hT : IsGeoTestTower (properNormalMarked Q) B := joint_added_boundary_test.2
  obtain ⟨V, hVc, hV, N, hLift, _, hlen, _, _, _, _⟩ :=
    exists_upper_native_test_history Q Q_domain B hT
  have hLift' : Lift (Nat.le_succ 2) (zeroPlane U) (plane_closed) (zeroPlane_regular U)
      Sec.E B V hVc hV N := hLift
  let A := nativeManifold (Nat.le_succ 2) V hV
  have hqV : q ∈ V := by
    rw [hLift'.carrier]
    exact joint_first_point_blowup_positive_normal_contact.2.2.2.2.2.2.1
  let z : A := ⟨q, hqV⟩
  have hSec : IsInvDomain 2 Sec := section_projected_domain _ Q.N Q.E Q.ideal Q.d Q_domain
  have hTrans : IsTransverse 3 (zeroPlane U) Sec.E :=
    isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor source_snc)
  have hSN : Sec.N ⊆ zeroPlane U := fun _ hx => ⟨mem_univ _, hx.2⟩
  have hI : IsInvDomain 2 N₀ :=
    isInvDomain_nativePullback (by decide : 0 < 3) (Nat.le_succ 2) (zeroPlane_regular U) Sec hSec hSN hTrans
  have hSecTest := ((properNormalMarked_locWPEquiv_section Q Q_domain).wEquiv.2 B).1.mp hT
  have hSE : IsSNCDivisor 3 Sec.E := hSec.isWellFormed.isSNCDivisor
  have hHol (u : X) (a : X → ℂ) (ha : Sec.ideal.mem u a) : HolomorphicAt 3 a u :=
    GermIdeal.IsCoherent.holomorphicAt_mem hSec.isWellFormed.isCoherent ha
  have hTest := HironakaActualNativeSectionNormalCrossings.Lift.native_test hLift' (by decide : 0 < 3) hSE hTrans Sec rfl hSN hHol hSecTest
  have hCosEq := HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift' (by decide : 0 < 3) hSE hTrans Sec rfl hSN hHol
  have hqSec := ((properNormalMarked_locWPEquiv_section Q Q_domain).wEquiv.2 B).2 hT ▸
    joint_added_boundary_survives_nonspecial.1
  have hz : z ∈ (geoTransformAlong N₀ N).cosupp := by rw [hCosEq]; exact hqSec
  have hBar := bar_local_any_boundary (X := Z) N₀ hI
  have hBarTest := (hBar.wEquiv.2 N).1.mp hTest
  have hzBar : z ∈ (geoTransformAlong (barMarked N₀) N).cosupp :=
    (hBar.wEquiv.2 N).2 hTest ▸ hz
  have hChron := actual_section_step_one_chronology U Q.N Q_domain.isWellFormed.isClosedSubmanifold_N
    Q.E source_snc Sec.ideal hSec.isWellFormed.isCoherent Q.d (T := B) (V := V) (Q := N) hLift'
  have hLevel : level N₀ N z = 1 :=
    ((hChron.2.2.1 z).1).symm.trans
      ((level_eq_of_E_eq (A := Sec) (B := M) rfl B q).trans joint_added_boundary_upper_regime_advances.2.1)
  have hRun : regimeRun (stepRegime N₀ 1) N z = 0 := by
    have hLe := (positive_normal_section_run Q Q_domain (s := 0) B hT q).1
    have hClock := hChron.2.2.2.2 1 z
    have hR := joint_added_boundary_upper_regime_advances.2.2
    rw [joint_added_boundary_upper_regime_advances.2.1] at hR
    exact Nat.eq_zero_of_le_zero (hClock ▸ hR ▸ hLe)
  let D₀ : Set A := (Subtype.val : V → Y) ⁻¹' D' 0
  let D₁ : Set A := (Subtype.val : V → Y) ⁻¹' D' 1
  let F₀ : Set A := (Subtype.val : V → Y) ⁻¹' F
  have hE : (geoTransformAlong (barMarked N₀) N).E = [D₀, D₁, F₀] := by
    have h := congrArg (fun K : MarkedIdeal 2 A => K.E) hChron.1
    exact h
  have ho : origMembers N₀ N = [D₀, D₁] := hChron.2.1.symm
  have hD : z ∈ D₀ := q_D
  have hD' : z ∉ D₁ := q_not_D1
  have hF : z ∈ F₀ := q_F
  have hne := strict_section_born_ne hLift'.carrier
  have hne' : F₀ ≠ D₁ := fun h => hD' (h ▸ hF)
  have hSecInit : Sec.cosupp = C := by
    have h := ((properNormalMarked_locWPEquiv_section Q Q_domain).wEquiv.2 T).2 trivial
    change M.cosupp = Sec.cosupp at h
    exact h.symm.trans joint_advanced_initial_cosupport
  have hNativeInit : N₀.cosupp.Subsingleton := by
    rw [cosupp_nativePullback (Nat.le_succ 2) (zeroPlane U) (zeroPlane_regular U) Sec hSN hHol, hSecInit]
    intro a ha b hb
    exact Subtype.ext ((mem_singleton_iff.mp ha).trans (mem_singleton_iff.mp hb).symm)
  have hCan := canonical_length_one N₀ (Seq.StepOneValueMasked.stepOneInvM R N₀) N hlen hTest hNativeInit
  refine ⟨V, hVc, hV, N, z, hLift', hlen, rfl, hz, hCan, ?_⟩
  exact native_read N₀ hI N hBarTest z hzBar hLevel hRun D₀ D₁ F₀ hE ho hD hD' hF hne hne'

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual advanced padded value differs from the native value on the
same lifted tower after any map preserving the lower first coordinate. -/
theorem joint_advanced_head_literal_native_no_shift :
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ x ∈ V, RegularAtDim (n := 3) V x 2)
      (N : BlowupTower Z (nativeManifold (Nat.le_succ 2) V hV))
      (z : nativeManifold (Nat.le_succ 2) V hV),
      Lift (Nat.le_succ 2) (zeroPlane U) (plane_closed) (zeroPlane_regular U)
        Sec.E B V hVc hV N ∧ N.length = 1 ∧ z.val = q ∧
      IsCanonical N₀ (Seq.StepOneValueMasked.stepOneInvM R N₀) N ∧
      ∀ f : ValTy 1 → ValTy 2, (∀ v, fstEntry (f v) = fstEntry v) →
        stepDimensionMap f (Seq.StepOneValueMasked.stepOneInvM R N₀ N z) ≠
        Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) M B q := by
  obtain ⟨V, hVc, hV, N, z, hLift, hLen, hPoint, _, hCan, hNative⟩ :=
    joint_advanced_head_literal_native_discrepancy
  refine ⟨V, hVc, hV, N, z, hLift, hLen, hPoint, hCan, ?_⟩
  intro f hf hEq
  have hP := joint_advanced_head_exact_upper_value
  rcases hNative with hTop | ⟨v, hv, hVal⟩
  · rw [hTop, hP] at hEq
    have he := congrArg (fun x : ℕ ×ₗ WithTop (ValTy 2) => (ofLex x).2) hEq
    exact WithTop.coe_ne_top he.symm
  · rw [hVal, hP] at hEq
    have he := WithTop.coe_injective
      (congrArg (fun x : ℕ ×ₗ WithTop (ValTy 2) => (ofLex x).2) hEq)
    have hFirst := congrArg (fstEntry (k := 1)) he
    exact (by decide : (0 : ℕ) ≠ 1) (hv.symm.trans ((hf v).symm.trans hFirst))

end
end Hironaka.HironakaG1LaterAdvancedHeadNativeExample
