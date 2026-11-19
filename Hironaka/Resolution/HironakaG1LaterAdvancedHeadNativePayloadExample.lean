import Hironaka.Resolution.HironakaG1LaterAdvancedHeadNativeValueExample
import Hironaka.Resolution.HironakaG1InitialPositiveNestedRead
import Hironaka.Resolution.HironakaActualNativeSectionOrder
import Hironaka.Resolution.HironakaActualNativeSectionPositiveLowerRecords
import Hironaka.Blowup.BlowupFunctionTransform
import Hironaka.Resolution.HironakaG1PositiveNormalChronology
import Hironaka.Resolution.HironakaG1NormalUnequalDepth
import Hironaka.Resolution.HironakaSharpActualCurveExceptionalPointExponent
import Hironaka.Resolution.HironakaG8GenericFullMonomial
import Hironaka.Resolution.HironakaG1ProperNormalPhaseNative
import Hironaka.Resolution.HironakaActualNativeSectionStepOneHistory
import Hironaka.Resolution.HironakaG1SupportedStepOne
import Hironaka.Resolution.HironakaG1LaterPositiveSuccessorRead
import Hironaka.Resolution.HironakaG1LaterSelectedActualOrder

/-! The monomial payload on the canonical advanced-head native lift. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterAdvancedHeadNativePayloadExample

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres StepOneValue StepOneValueMasked StepOneRegime
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaRelativeNormalIdeal HironakaG1ProperCarrierNormalContact
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
  HironakaG1LaterAdvancedHeadNativeExample HironakaG1LaterPositiveSelectedExample
  BlowupFunctionTransform BlowupControlledTransform GermIdealPullbackCalculus
  InvertibleIdealQuotient RelativePrincipalizationSpan MemberInterLocusAlong
  MonomialCaseAlong BlowupConstruction BlowupStrictIdeal IdealWeightPowers
  HironakaG1LaterAdvancedHeadNativeValueExample HironakaActualNativeSectionOrder
  HironakaSharpOriginalProductTraceOrder RestrictedIdealQuotient RestrictedIdealExtension
  MonomialPartEtale MarkedIdealOperationsAlong
  HironakaG1InitialPositiveNestedRead HironakaG1NormalNestedOrderMap
  AnalyticIrreducibleComponents MonomialCase DivisorExponentAlong DerivativeIdealAlongEtale SubmanifoldChartedSpace
  HironakaG1LaterAdvancedHeadNativeExample
  HironakaActualNativeSectionRegularity InvDomainMemberRestriction

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

private abbrev chartOpen : Opens Y := ⟨yChart.source, yChart.isOpen_source⟩
private abbrev u (z : Y) : ℂ := yChart.toFun z (1 : Fin 3)

private def axis (a : ℂ) : Y :=
  yChart.invFun (a • EuclideanSpace.single (1 : Fin 3) (1 : ℂ))

private theorem axis_near : Tendsto axis (𝓝 0) (𝓝 q) := by
  let v := EuclideanSpace.single (1 : Fin 3) (1 : ℂ)
  have hf : Continuous (fun a : ℂ => a • v) := continuous_id.smul continuous_const
  have hAt : Tendsto (fun a : ℂ => a • v) (𝓝 0) (𝓝 (yChart.toFun q)) := by
    simpa [chart_q.2] using hf.tendsto (0 : ℂ)
  exact (yChart.homeo.tendsto_symm chart_q.1).comp hAt

private theorem axis_geometry (a : ℂ) (ha : a ≠ 0) :
    axis a ∈ chartOpen ∧ axis a ∈ D' 0 ∧
      axis a ∈ HomogenizedGlueingTower.strictAlong B (zeroPlane U) ∧ u (axis a) = a := by
  let v := EuclideanSpace.single (1 : Fin 3) (1 : ℂ)
  have htarget := chart_all (a • v)
  have hw : axis a ∈ chartOpen := yChart.toPartialEquiv.map_target htarget
  have hc : yChart.toFun (axis a) = a • v := yChart.toPartialEquiv.right_inv htarget
  have hproj : (π (axis a)).val = monomial 0 (1 : Fin 3) (a • v) := by
    rw [chart_projection _ hw, hc]
  have hp0 : p.val = 0 := map_zero (tangentInclusion 2 1)
  have hOff : π (axis a) ∉ C := by
    intro hp
    have h := congrArg (fun x : X => x.val (1 : Fin 3)) (mem_singleton_iff.mp hp)
    change (π (axis a)).val (1 : Fin 3) = p.val (1 : Fin 3) at h
    rw [hproj, hp0, monomial_apply] at h
    exact ha (by simpa [v] using h)
  refine ⟨hw, (strict_chart_coordinate 0 (by decide) _ hw).mpr ?_, ?_, ?_⟩
  · rw [hc]
    simp [v]
  · change axis a ∈ geoStrictTransform π C (zeroPlane U)
    apply subset_closure
    change π (axis a) ∈ zeroPlane U \ C
    refine ⟨⟨mem_univ _, ?_⟩, hOff⟩
    ext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    rw [hj]
    change (π (axis a)).val (2 : Fin 3) = 0
    rw [hproj, monomial_apply]
    simp [v]
  · change yChart.toFun (axis a) (1 : Fin 3) = a
    rw [hc]
    simp [v]


private theorem Sec_domain : IsInvDomain 2 Sec :=
  section_projected_domain _ Q.N Q.E Q.ideal Q.d Q_domain

private theorem Sec_bar : barMarked Sec = Sec := by
  change coeffMarkedAlong (homMarkedAlong Sec) = Sec
  rw [homMarkedAlong_eq_of_mark_one Sec rfl Sec_domain.isWellFormed.isCoherent,
    coeffMarkedAlong_eq_of_mark_one Sec rfl Sec_domain.isWellFormed.isCoherent]

private theorem section_square {z : X} :
    Sec.ideal.mem z (fun w : X => w.val (1 : Fin 3) ^ 2) := by
  change (sectionMarked sourceRecord).ideal.mem z _
  rw [section_source_generators]
  let f : ComplexModel 3 → ℂ := fun w => w (1 : Fin 3) ^ 2
  have hf : HolomorphicAt 3 f z.val := Eventually.of_forall fun _ =>
    ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).mdifferentiable.pow 2).mdifferentiableAt
  have hEq : f = coordinatePairGenerator false ∘ tangentProjection 2 1 := rfl
  refine GermIdeal.mem_pullback_iff.mpr
    (isInSpanAt_self ⟨f, isInSpanAt_self ⟨false, hEq⟩ hf, rfl⟩ ?_)
  exact hf.comp_contMDiff (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)

private theorem Sec_middle_member {z : Y} (hz : z ∈ chartOpen) :
    (geoTransformAlong Sec B).ideal.mem z u := by
  have hControl : (controlledTransform hπ Sec.ideal 1).mem z u := by
    refine mem_controlledTransform_of_eq_pow_mul equation_on_chart hz section_square
      (yChart.holomorphicAt_coord hz 1) ?_
    filter_upwards [chartOpen.isOpen.mem_nhds hz] with w hw
    change ((π w).val (1 : Fin 3)) ^ 2 = exceptionalCoordinate w ^ 1 * u w
    rw [chart_projection w hw, monomial_apply, exceptionalCoordinate_coord w hw]
    simp [u, pow_two]
  change (colonAlong 3 (geoStrictTransform π C Sec.N) (GermIdeal.pullback π Sec.ideal)
    (idealPow (GermIdeal.pullback π (vanishingIdeal (n := 3) C)) 1)).mem z u
  have hN := mem_colon_iff.mp hControl
  refine ⟨hN.1, fun g hg => ?_⟩
  exact le_restrictOn (isCoherent_pullback hπ.contMDiff Sec_domain.isWellFormed.isCoherent)
    z _ (hN.2 _ hg)

private def axisProjection : ComplexModel 3 →L[ℂ] ComplexModel 3 :=
  (ContinuousLinearMap.smulRight (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3))
    (EuclideanSpace.single (1 : Fin 3) (1 : ℂ)))

private def chart : ComplexChart 3 Y :=
  ⟨yChart.homeo, atlasHomeo_mem_atlas yChart.toPartialEquiv (Or.inl ⟨yChart, rfl⟩)⟩

private theorem axis_not_order_two {S : Set Y} (hq : q ∈ S)
    (h : ∀ a : ℂ, a ≠ 0 → axis a ∈ S) :
    ¬ VanishesToOrderOn 3 S q 2 u := by
  intro hOrd
  let θ : ComplexModel 3 → Y := fun w => yChart.invFun (axisProjection w)
  have hθ₀ : θ 0 = q := by
    change yChart.invFun (axisProjection 0) = yChart.invFun 0
    rw [map_zero]
  have hθ : ∀ᶠ w : ComplexModel 3 in 𝓝 0,
      MDifferentiableAt 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) θ w := by
    apply Eventually.of_forall
    intro w
    have hT : axisProjection w ∈ chart.val.target := chart_all _
    exact (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel 3)) chart.property hT).comp w
      axisProjection.mdifferentiableAt
  have hθS (w : ComplexModel 3) : θ w ∈ S := by
    change axis (w (1 : Fin 3)) ∈ S
    by_cases hw : w (1 : Fin 3) = 0
    · have h₀ : axis 0 = q := by
        change yChart.invFun ((0 : ℂ) • EuclideanSpace.single (1 : Fin 3) 1) = yChart.invFun 0
        rw [zero_smul]
      rw [hw, h₀]
      exact hq
    · exact h _ hw
  have hθu (w : ComplexModel 3) : u (θ w) = w (1 : Fin 3) := by
    have hc : yChart.toFun (θ w) = axisProjection w :=
      yChart.toPartialEquiv.right_inv (chart_all _)
    change yChart.toFun (θ w) (1 : Fin 3) = _
    rw [hc]
    simp [axisProjection]
  have hV : VanishesToOrderOn 3 S (θ 0) 2 u := hθ₀.symm ▸ hOrd
  obtain ⟨b, hb, hEq⟩ := vanishesToOrderOn_comp (θ := θ) (p := (0 : ComplexModel 3)) hθ hV
  have he : (fun w : ComplexModel 3 => w (1 : Fin 3)) =ᶠ[𝓝 0] b := by
    filter_upwards [hEq] with w hw
    exact (hθu w).symm.trans (hw (hθS w))
  let Φ : LocalHolomorphicEquivAt (n := 3) (chartAt (ComplexModel 3) (0 : ComplexModel 3) 0) :=
    BlowupExistenceOriginIdeal.idEquivAt
  exact MonomialCase.flatCoord_notMem_idealPow_two Φ 1 (mem_flatDomain_self Φ)
    (OrderTaylor.mem_idealPow_congr hb he.symm)

private theorem curve_rank_one {A : CMfd.{0} 2} (K : MarkedIdeal 2 A)
    (hK : IsInvDomain 1 K) {z : A} (hz : z ∈ K.cosupp) :
    RegularAtDim (n := 2) K.N z 1 := by
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
  exact hr

private abbrev bornGamma : WithBot MonomialInvariant.Val :=
  ↑(toLex (1, toLex (1, toColex ({1} : Finset ℕ))))

private theorem single_born_gamma {A : CMfd.{0} 2} (J : MarkedIdeal 2 A)
    (hJ : IsInvDomain 1 J) (H : Set A) (hE : J.E = [∅, H]) (hd : J.d = 1)
    {x : A} (hx : x ∈ J.cosupp) (hH : x ∈ H)
    (hOrd : ordinaryTraceOrder J.N J.ideal x = 1) :
    gammaAlong 2 J.N J.ideal J.E J.d x = bornGamma := by
  have hI : H ∈ J.E := by rw [hE]; simp
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hI
  have hi' : x ∈ J.E.get i := hi.symm ▸ hH
  have hRank := curve_rank_one J hJ hx
  have hexp := actual_curve_member_divExp_eq_ordinaryTraceOrder (by decide : 0 < 2)
    hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isSNCDivisor hJ.isWellFormed.isTransverse
    hJ.isWellFormed.isCoherent hJ.isNonzeroAlongAt hRank i hi'
  have hExp : divExpAlong 2 J.N J.ideal H x = 1 := by rw [← hi, hexp, hOrd]
  have hMembers : memberIdx J.E x = {1} := by
    rw [hE]
    ext t
    rw [mem_memberIdx, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, hm⟩
      have ht' : t < 2 := ht
      have he : t = 0 ∨ t = 1 := by omega
      rcases he with rfl | rfl
      · exact hm.elim
      · rfl
    · rintro rfl
      exact ⟨by simp, hH⟩
  let ex := expDataAlong 2 J.N J.ideal J.E x
  have hOne : ex 1 = 1 := by
    change expDataAlong 2 J.N J.ideal J.E x 1 = 1
    unfold expDataAlong
    have hlt : (1 : ℕ) < J.E.length := by rw [hE]; simp
    rw [dif_pos hlt]
    have hGet : J.E.get ⟨1, hlt⟩ = H := by
      rw [List.get_eq_getElem]
      simp [hE]
    rw [hGet, hExp]
  have hFeas : MonomialInvariant.feasible {1} ex 1 = {{1}} := by
    ext K
    rw [MonomialInvariant.mem_feasible, Finset.mem_singleton]
    constructor
    · intro h
      have hne : K.Nonempty := by
        by_contra hn
        rw [Finset.not_nonempty_iff_eq_empty.mp hn] at h
        simp at h
      obtain ⟨t, ht⟩ := hne
      obtain rfl := Finset.mem_singleton.mp (h.1 ht)
      exact Finset.Subset.antisymm h.1 (Finset.singleton_subset_iff.mpr ht)
    · rintro rfl
      simp [hOne]
  unfold gammaAlong
  rw [hMembers, hd]
  change MonomialInvariant.inv 2 {1} ex 1 = _
  unfold MonomialInvariant.inv
  rw [hFeas]
  simp [MonomialInvariant.key, hOne, bornGamma]

set_option maxHeartbeats 1900000 in
set_option backward.isDefEq.respectTransparency false in
/-- At the canonical native survivor the sole incident selected slot is
the born slot of index one. It has exponent one, giving the exact
monomial key `(1, 1, {1})`. -/
theorem joint_advanced_head_native_numerical_payload :
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ x ∈ V, RegularAtDim (n := 3) V x 2)
      (N : BlowupTower Z (nativeManifold (Nat.le_succ 2) V hV))
      (z : nativeManifold (Nat.le_succ 2) V hV),
      Lift (Nat.le_succ 2) (zeroPlane U) plane_closed (zeroPlane_regular U)
        Sec.E B V hVc hV N ∧ N.length = 1 ∧ z.val = q ∧
      IsCanonical N₀ (Seq.StepOneValueMasked.stepOneInvM R N₀) N ∧
      Seq.StepOneValueMasked.stepOneInvM R N₀ N z =
        toLex (1, (↑(show ValTy 1 from toLex (0, toLex (Sum.inl bornGamma))) : WithTop (ValTy 1))) := by
  obtain ⟨V, hVc, hV, N, z, hLift, hlen, hq, hCos, hCan, hNS, _, hz, _, hVal⟩ :=
    joint_advanced_head_exact_native_monomial_read
  let A := nativeManifold (Nat.le_succ 2) V hV
  let G := geoTransformAlong (barMarked N₀) N
  let K := memberRestrict G (membersThrough G.E (origMembers N₀ N) z)
  let O := maskA N₀ N z
  let J := lowerMarkedM N₀ 1 N z
  let W := CMfd.of (n := 2) O
  let x : O := ⟨z, hz⟩
  let i : A → Y := Subtype.val
  let H₀ : Set A := i ⁻¹' D' 0
  let H₁ : Set A := i ⁻¹' D' 1
  let Hf : Set A := i ⁻¹' F
  have hQ : IsInvDomain 2 Q := Q_domain
  have hTestP : IsGeoTestTower (properNormalMarked Q) B := joint_added_boundary_test.2
  have hTestSec := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 B).1.mp hTestP
  have hTrans : IsTransverse 3 (zeroPlane U) Sec.E :=
    isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hSupport : Sec.N ⊆ zeroPlane U := fun _ hx => ⟨mem_univ _, hx.2⟩
  have hDom : IsInvDomain 2 N₀ :=
    isInvDomain_nativePullback (by decide : 0 < 3) (Nat.le_succ 2) (zeroPlane_regular U)
      Sec Sec_domain hSupport hTrans
  have hTest := HironakaActualNativeSectionNormalCrossings.Lift.native_test hLift
    (by decide : 0 < 3) Sec_domain.isWellFormed.isSNCDivisor hTrans Sec rfl hSupport
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem Sec_domain.isWellFormed.isCoherent hg) hTestSec
  have hBar := bar_local_any_boundary (X := Z) N₀ hDom
  have hBarTest := (hBar.wEquiv.2 N).1.mp hTest
  have hGcos : z ∈ G.cosupp := (hBar.wEquiv.2 N).2 hTest ▸ hCos
  have hG : G.IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (isWellFormed_barMarked N₀ hDom.isWellFormed) N hBarTest
  have hChron := actual_section_step_one_chronology U Q.N hQ.isWellFormed.isClosedSubmanifold_N
    Q.E hQ.isWellFormed.isSNCDivisor Sec.ideal Sec_domain.isWellFormed.isCoherent Q.d
    (T := B) (V := V) (Q := N) hLift
  have hLiftN : V = HomogenizedGlueingTower.strictAlong B (zeroPlane U) := hLift.carrier
  have hActual : G = nativePullback (Nat.le_succ 2) V hV (geoTransformAlong Sec B) := by
    have h := hChron.1
    change G = nativePullback (Nat.le_succ 2) V hV (geoTransformAlong (barMarked Sec) B) at h
    rwa [Sec_bar] at h
  have hGd : G.d = 1 := by rw [hActual]; rfl
  have hGN : G.N = univ := by
    rw [hActual]
    change i ⁻¹' geoStrictTransform π C Sec.N = univ
    have hN : Sec.N = zeroPlane U := rfl
    rw [hN]
    change i ⁻¹' HomogenizedGlueingTower.strictAlong B (zeroPlane U) = univ
    rw [← hLiftN]
    exact Set.eq_univ_of_forall fun a => a.property
  have hGE : G.E = [H₀, H₁, Hf] := by rw [hActual]; rfl
  have hOrig : origMembers N₀ N = [H₀,H₁] := hChron.2.1.symm
  have hzD : z ∈ H₀ := by change z.val ∈ D' 0; rw [hq]; exact q_D
  have hzD' : z ∉ H₁ := by change z.val ∉ D' 1; rw [hq]; exact q_not_D1
  have hzF : z ∈ Hf := by change z.val ∈ F; rw [hq]; exact q_F
  have hF0 : Hf ≠ H₀ := by
    obtain ⟨hv, hD, hS, hu⟩ := axis_geometry 1 one_ne_zero
    let w : V := ⟨axis 1, hLiftN.symm ▸ hS⟩
    intro he
    have hw : w ∈ H₀ := hD
    have hwF : π (axis 1) ∈ C := by
      exact (show w ∈ Hf from he.symm ▸ hw)
    have hp0 : p.val = 0 := map_zero (tangentInclusion 2 1)
    have hπ0 := congrArg (fun x : X => x.val (1 : Fin 3)) (mem_singleton_iff.mp hwF)
    change (π (axis 1)).val (1 : Fin 3) = p.val (1 : Fin 3) at hπ0
    rw [chart_projection _ hv, monomial_apply, hp0] at hπ0
    have h00 : u (axis 1) = 0 := by simpa [u] using hπ0
    exact one_ne_zero (hu.symm.trans h00)
  have hF1 : Hf ≠ H₁ := fun he => hzD' (he ▸ hzF)
  have hKN : K.N = H₀ := by
    have hs : ∀ H ∈ origMembers N₀ N, H ∈ G.E := fun _ ha => List.mem_of_mem_take ha
    rw [memberRestrict_N, hGN, univ_inter, memberInter_membersThrough hs, hOrig]
    ext y
    constructor
    · intro hy
      exact hy _ (by simp) hzD
    · intro hy H hH hzH
      rcases List.mem_cons.mp hH with rfl | hH
      · exact hy
      · rw [List.mem_singleton] at hH
        exact (hzD' (hH ▸ hzH)).elim
  have hKE : K.E = [H₁,Hf] := by
    classical
    rw [memberRestrict_membersThrough_E, hGE, hOrig]
    simp [hzD, hzD', hF0, hF1]
  have hKI : K.ideal = G.ideal := by
    rw [memberRestrict_ideal, coeffMarkedAlong_eq_of_mark_one G hGd hG.isCoherent]
  have hKWF : K.IsWellFormed := isWellFormed_memberRestrict (by decide) hG _
  have hKcos : z ∈ K.cosupp := by
    rw [cosupp_memberRestrict hG hGd.ge]
    exact ⟨hGcos, fun _ h => (mem_membersThrough.mp h).2⟩
  have hLevel : level N₀ N z = 1 := by
    have h := (hChron.2.2.1 z).1
    change level Sec B z.val = level N₀ N z at h
    rw [hq] at h
    exact h.symm.trans ((level_eq_of_E_eq (A := Sec) (B := M) rfl B q).trans
      joint_added_boundary_upper_regime_advances.2.1)
  have hJ : IsInvDomain 1 J :=
    isInvDomain_lowerMarked_succ N₀ hDom.isWellFormed hDom.one_le_d (by decide) N hBarTest hDom.dimLE hLevel
  have hJd : J.d = 1 := by
    change (coeffMarkedAlong G).d = 1
    rw [coeffMarkedAlong_eq_of_mark_one G hGd hG.isCoherent, hGd]
  have hxJ : x ∈ J.cosupp := by
    change x ∈ (MarkedIdeal.pullback (Subtype.val : O → A) K).cosupp
    rw [cosupp_pullback_val K (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hKWF.isCoherent hg) O]
    exact hKcos
  have hJE : J.E = [∅, (Subtype.val : O → A) ⁻¹' Hf] := by
    change K.E.map ((Subtype.val : O → A) ⁻¹' ·) = _
    rw [hKE]
    have hMiss : (Subtype.val : O → A) ⁻¹' H₁ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hyM := (interior_subset y.property).1
      exact hzD' (hyM _ (by rw [hOrig]; simp) hy)
    change [(Subtype.val : O → A) ⁻¹' H₁, (Subtype.val : O → A) ⁻¹' Hf] = _
    rw [hMiss]
  have hzChart : z.val ∈ chartOpen := hq.symm ▸ chart_q.1
  have hUmem : K.ideal.mem z (u ∘ i) := by
    let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ 2) hV
    have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ 2) hV
    rw [hKI, hActual]
    change (GermIdeal.pullback (m := 2) i (geoTransformAlong Sec B).ideal).mem z (u ∘ i)
    have hHol : HolomorphicAt 2 (u ∘ i) z :=
      (yChart.holomorphicAt_coord hzChart 1).comp_contMDiff
        (Eventually.of_forall fun _ => (contMDiff_val (Nat.le_succ 2) hV).contMDiffAt)
    exact GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨u, Sec_middle_member hzChart, rfl⟩ hHol)
  have hGE2 : ¬ VanishesToOrderOn 2 K.N z 2 (u ∘ i) := by
    intro hHigh
    have hVanish := (vanishesToOrderOn_native_iff (Nat.le_succ 2) hV K.N z 2 u).mpr hHigh
    rw [hq] at hVanish
    refine axis_not_order_two (S := i '' K.N) ⟨z, hKcos.1, hq⟩ ?_ hVanish
    intro a ha
    obtain ⟨_, haD, haS, _⟩ := axis_geometry a ha
    let w : V := ⟨axis a, hLiftN.symm ▸ haS⟩
    refine ⟨w, ?_, rfl⟩
    rw [hKN]
    exact haD
  have hxNot : x ∉ cosupport 2 J.N J.ideal 2 := by
    intro hx
    have hEquiv := MonomialPartEtale.cosupport_pullback_of_local
      (φ := (Subtype.val : O → A))
      (fun y => ⟨openInv O y, isLocalInverseAt_val (n := 2) O y⟩)
      (𝔞 := K.ideal) (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hKWF.isCoherent hg) K.N 2
    have hz2 : z ∈ cosupport 2 K.N K.ideal 2 := by
      have hx' := hx
      change x ∈ cosupport 2 ((Subtype.val : O → A) ⁻¹' K.N)
        (GermIdeal.pullback (m := 2) (Subtype.val : O → A) K.ideal) 2 at hx'
      rw [hEquiv] at hx'
      exact hx'
    exact hGE2 (hz2.2 _ hUmem)
  have hOrd (r : ℕ) := ordinaryTraceOrder_cosupport_iff (X := W) (W := J.N) (I := J.ideal) (x := x) hJ.isWellFormed.isClosedSubmanifold_N
    hJ.isWellFormed.isCoherent hJ.isNonzeroAlongAt hxJ.1 r
  have hOrd1 : ordinaryTraceOrder (X := W) J.N J.ideal x = 1 := by
    have hx1 : x ∈ cosupport 2 J.N J.ideal 1 := by
      have h := hxJ
      change x ∈ cosupport 2 J.N J.ideal J.d at h
      rwa [hJd] at h
    have hlb := (hOrd 1).mp hx1
    have hub := mt (hOrd 2).mpr hxNot
    omega
  have hGamma := single_born_gamma (A := W) J hJ _ hJE hJd hxJ hzF hOrd1
  refine ⟨V, hVc, hV, N, z, hLift, hlen, hq, hCan, ?_⟩
  exact hVal.trans (congrArg (fun γ : WithBot MonomialInvariant.Val =>
    toLex (1, (↑(show ValTy 1 from toLex (0, toLex (Sum.inl γ))) : WithTop (ValTy 1)))) hGamma)

private abbrev pN : Z := ⟨p, ⟨mem_univ _, HironakaActualCentreJointJets.actualJointNormalProjection_tangent 2 1 0⟩⟩
private abbrev T₀ : BlowupTower Z Z := .refl

private theorem section_initial_special : IsSpecial Sec T p := by
  have hQ : IsInvDomain 2 Q := Q_domain
  have hSec0 : Sec.cosupp = C := by
    have h := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 T).2 trivial
    change M.cosupp = Sec.cosupp at h
    exact h.symm.trans joint_advanced_initial_cosupport
  have hLev : level Sec T p = 2 :=
    (level_eq_of_E_eq (A := Sec) (B := M) rfl T p).trans joint_added_boundary_upper_regime_advances.1
  right
  refine ⟨hLev ▸ (by decide : 1 ≤ (2 : ℕ)), ?_⟩
  change p ∈ memberInterLocus (barMarked Sec).N (origMembers Sec T) (barMarked Sec).cosupp
  have hOld : origMembers Sec T = [D 0,D 1] := rfl
  rw [Sec_bar, hOld, hSec0]
  refine mem_memberInterLocus_iff.mpr ⟨mem_singleton _, Eventually.of_forall fun y hy hOld => ?_⟩
  have hp0 : p.val = 0 := map_zero (tangentInclusion 2 1)
  have h0 : y.val (0 : Fin 3) = 0 :=
    hOld (D 0) (by simp) (show p.val (0 : Fin 3) = 0 by rw [hp0]; rfl)
  have h1 : y.val (1 : Fin 3) = 0 :=
    hOld (D 1) (by simp) (show p.val (1 : Fin 3) = 0 by rw [hp0]; rfl)
  have h2 : y.val (2 : Fin 3) = 0 :=
    congrArg (fun w : ComplexModel 1 => w (0 : Fin 1)) hy.2
  apply mem_singleton_iff.mpr
  apply Subtype.ext
  rw [hp0]
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem padded_initial_nonspecial : ¬ IsSpecial M T p := by
  intro hSp
  have hLevel := joint_added_boundary_upper_regime_advances.1
  rcases hSp with h | ⟨_, h⟩
  · exact (by decide : (2 : ℕ) ≠ 0) (hLevel.symm.trans h.1)
  change p ∈ memberInterLocus (barMarked M).N (origMembers M T) (barMarked M).cosupp at h
  have hM : IsInvDomain 3 M := joint_added_boundary_test.1
  have hBar : barMarked M = M := by
    change coeffMarkedAlong (homMarkedAlong M) = M
    rw [homMarkedAlong_eq_of_mark_one M rfl hM.isWellFormed.isCoherent,
      coeffMarkedAlong_eq_of_mark_one M rfl hM.isWellFormed.isCoherent]
  have hE : origMembers M T = [D 0, D 1] := rfl
  rw [hBar, hE, joint_advanced_initial_cosupport] at h
  let v := EuclideanSpace.single (2 : Fin 3) (1 : ℂ)
  let f (a : ℂ) : X := ⟨a • v, mem_univ _⟩
  have hfp : f 0 = p := by
    apply Subtype.ext
    change (0 : ℂ) • v = p.val
    rw [show p.val = 0 from map_zero (tangentInclusion 2 1), zero_smul]
  have hfCont : Continuous f := (continuous_id.smul continuous_const).subtype_mk _
  have hf : Tendsto f (𝓝 0) (𝓝 p) := by rw [← hfp]; exact hfCont.tendsto _
  have hne : ∃ᶠ a : ℂ in 𝓝 0, a ≠ 0 := by
    have hF : ∃ᶠ a : ℂ in 𝓝[≠] 0, True :=
      Filter.Eventually.frequently (Filter.Eventually.of_forall fun _ => trivial)
    exact ((frequently_nhdsWithin_iff).mp hF).mono (fun _ ha => ha.2)
  obtain ⟨a, ha, hA⟩ := (hne.and_eventually (hf.eventually (mem_memberInterLocus_iff.mp h).2)).exists
  have haC : f a ∈ C := by
    apply hA (mem_univ _)
    intro H hH _
    rcases List.mem_cons.mp hH with rfl | hH
    · change (a • v) (0 : Fin 3) = 0
      simp [v]
    · rw [List.mem_singleton] at hH
      subst H
      change (a • v) (1 : Fin 3) = 0
      simp [v]
  have he := congrArg (fun x : X => x.val (2 : Fin 3)) (mem_singleton_iff.mp haC)
  change (a • v) (2 : Fin 3) = p.val (2 : Fin 3) at he
  rw [show p.val = 0 from map_zero (tangentInclusion 2 1)] at he
  exact ha (by simpa [v] using he)


set_option maxHeartbeats 1300000 in
set_option backward.isDefEq.respectTransparency false in
/-- Both initial values are exact at the common origin. The initial native
level-two special value recodes to the padded order-one insertion. -/
theorem joint_advanced_head_initial_exact_comparison :
    Seq.StepOneValueMasked.stepOneInvM R N₀ T₀ pN = toLex (2, (⊤ : WithTop (ValTy 1))) ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) M T p =
        toLex (2, (↑(positiveSuccessorRead 1 (toLex (0, (⊤ : WithTop (ValTy 1))))) :
          WithTop (ValTy 2))) := by
  have hLift : Lift (Nat.le_succ 2) (zeroPlane U) plane_closed (zeroPlane_regular U)
      Sec.E T (zeroPlane U) plane_closed (zeroPlane_regular U) T₀ := .refl
  have hp : p ∈ M.cosupp := by rw [joint_advanced_initial_cosupport]; exact mem_singleton _
  obtain ⟨hN, hP⟩ := original_initial_positive_special_nested_read (q := 1) (s := 1)
    (by decide : 0 < 2) Q Q_domain hLift pN hp joint_added_boundary_upper_regime_advances.1
    padded_initial_nonspecial section_initial_special id
  refine ⟨hN, ?_⟩
  have hBar : barMarked M = M := by
    change coeffMarkedAlong (homMarkedAlong M) = M
    have hI := joint_added_boundary_test.1.isWellFormed.isCoherent
    rw [homMarkedAlong_eq_of_mark_one M rfl hI, coeffMarkedAlong_eq_of_mark_one M rfl hI]
  have hD : (coeffMarkedAlong (barMarked M)).d = 1 := by
    rw [hBar, coeffMarkedAlong_eq_of_mark_one M rfl joint_added_boundary_test.1.isWellFormed.isCoherent]
    rfl
  change Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) M T p =
    nestedStep (fun _ => (coeffMarkedAlong (barMarked M)).d) id
      (Seq.StepOneValueMasked.stepOneInvM R N₀ T₀ pN) at hP
  rw [hN, hD] at hP
  exact hP

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The level-zero insertion recodes the initial values on the actual lift.
At the attained later anchor every such insertion fails, even if its order
and its finite-letter map are allowed to vary. -/
theorem joint_advanced_head_nested_recoding_changes_on_history :
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ x ∈ V, RegularAtDim (n := 3) V x 2)
      (N : BlowupTower Z (nativeManifold (Nat.le_succ 2) V hV))
      (z : nativeManifold (Nat.le_succ 2) V hV),
      Lift (Nat.le_succ 2) (zeroPlane U) plane_closed (zeroPlane_regular U)
        Sec.E B V hVc hV N ∧ N.length = 1 ∧ z.val = q ∧ N.proj z = pN ∧
      let RP := invFamily (by decide : 0 < 3) 2
      nestedStep (fun _ => 1) id (Seq.StepOneValueMasked.stepOneInvM R N₀ T₀ (N.proj z)) =
        Seq.StepOneValueMasked.stepOneInvM RP M T p ∧
      ∀ (orderAtLevel : ℕ → ℕ) (δ : ValTy 1 → ValTy 1),
        nestedStep orderAtLevel δ (Seq.StepOneValueMasked.stepOneInvM R N₀ N z) ≠
          Seq.StepOneValueMasked.stepOneInvM RP M B q := by
  obtain ⟨V, hVc, hV, N, z, hLift, hLen, hq, _, hNative⟩ := joint_advanced_head_native_numerical_payload
  have hProj : N.proj z = pN := by
    apply Subtype.ext
    change (N.proj z).val = p
    rw [← hLift.square z, hq]
    exact q_proj
  refine ⟨V, hVc, hV, N, z, hLift, hLen, hq, hProj, ?_, ?_⟩
  · rw [hProj, joint_advanced_head_initial_exact_comparison.1,
      joint_advanced_head_initial_exact_comparison.2]
    rfl
  · intro o δ he
    let v : ValTy 1 := toLex (0, toLex (Sum.inl bornGamma))
    have hn : Seq.StepOneValueMasked.stepOneInvM R N₀ N z =
        toLex (1, (v : WithTop (ValTy 1))) := hNative
    rw [hn] at he
    simp only [nestedStep, ofLex_toLex, nestedLower_coe] at he
    have he' := he
    rw [joint_advanced_head_exact_upper_value] at he'
    have hc := WithTop.coe_injective
      (congrArg (fun x : ℕ ×ₗ WithTop (ValTy 2) => (ofLex x).2) he')
    have ho : o 1 = 1 := congrArg (fstEntry (k := 1)) hc
    rw [ho] at he
    exact joint_advanced_canonical_not_level_zero_inner (↑(δ v)) he.symm

end
end Hironaka.HironakaG1LaterAdvancedHeadNativePayloadExample
