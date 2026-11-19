import Hironaka.Resolution.HironakaG1LaterAdvancedHeadNativeExample
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

/-! The exact native branch on the canonical advanced-head lift. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterAdvancedHeadNativeValueExample

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
  HironakaG1LaterAdvancedHeadNativeExample HironakaG1LaterPositiveSelectedExample
  BlowupFunctionTransform BlowupControlledTransform GermIdealPullbackCalculus
  InvertibleIdealQuotient RelativePrincipalizationSpan MemberInterLocusAlong
  MonomialCaseAlong BlowupConstruction BlowupStrictIdeal IdealWeightPowers

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

private theorem source_square {z : X} :
    M.ideal.mem z (fun w : X => w.val (1 : Fin 3) ^ 2) := by
  change P.ideal.mem z (paddedGenerator (.inl false) ∘ (Subtype.val : X → ComplexModel 3))
  rw [proper_source_generators]
  have hHol : HolomorphicAt 3 (paddedGenerator (.inl false)) z.val :=
    Eventually.of_forall fun w => paddedGenerator_hol (.inl false) w
  exact GermIdeal.mem_pullback_iff.mpr
    (isInSpanAt_self ⟨paddedGenerator (.inl false), isInSpanAt_self ⟨.inl false, rfl⟩ hHol, rfl⟩
      (hHol.comp_contMDiff (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)))

private theorem controlled_middle_coordinate {z : Y} (hz : z ∈ chartOpen) :
    (geoTransformAlong M B).ideal.mem z u := by
  change (M.geoTransform C π).ideal.mem z u
  rw [geoTransform_ideal_eq_controlledTransform (𝔪 := M) (show M.N = univ from preimage_univ)
    joint_added_boundary_test.1.isWellFormed.isCoherent hπ]
  change (controlledTransform hπ M.ideal 1).mem z u
  refine mem_controlledTransform_of_eq_pow_mul equation_on_chart hz source_square
    (yChart.holomorphicAt_coord hz 1) ?_
  filter_upwards [chartOpen.isOpen.mem_nhds hz] with w hw
  change ((π w).val (1 : Fin 3)) ^ 2 = exceptionalCoordinate w ^ 1 * u w
  rw [chart_projection w hw, monomial_apply, exceptionalCoordinate_coord w hw]
  simp [u, pow_two]

private theorem proper_cosupp_middle_zero {z : Y} (hz : z ∈ chartOpen)
    (hzC : z ∈ (geoTransformAlong M B).cosupp) : u z = 0 := by
  exact (vanishesToOrderOn_one_iff hzC.1 (yChart.holomorphicAt_coord hz 1)).mp
    (hzC.2 _ (controlled_middle_coordinate hz))

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

private theorem native_source_domain : IsInvDomain 2 Q := Q_domain

private theorem Sec_domain : IsInvDomain 2 Sec :=
  section_projected_domain _ Q.N Q.E Q.ideal Q.d native_source_domain

private theorem Sec_bar : barMarked Sec = Sec := by
  change coeffMarkedAlong (homMarkedAlong Sec) = Sec
  rw [homMarkedAlong_eq_of_mark_one Sec rfl Sec_domain.isWellFormed.isCoherent,
    coeffMarkedAlong_eq_of_mark_one Sec rfl Sec_domain.isWellFormed.isCoherent]

private theorem upper_test : IsGeoTestTower (properNormalMarked Q) B := joint_added_boundary_test.2
private abbrev hLocalEquiv := properNormalMarked_locWPEquiv_section Q native_source_domain

private theorem Sec_test : IsGeoTestTower Sec B := ((hLocalEquiv.wEquiv.2 B).1.mp upper_test)
private theorem Sec_cosupp_eq : (geoTransformAlong M B).cosupp = (geoTransformAlong Sec B).cosupp :=
  (hLocalEquiv.wEquiv.2 B).2 upper_test

private theorem Sec_level : level Sec B q = 1 :=
  (level_eq_of_E_eq (A := Sec) (B := M) rfl B q).trans joint_added_boundary_upper_regime_advances.2.1

/-- The same survivor on the literal section is nonspecial. The punctured
middle axis stays in the strict original member and leaves its cosupport. -/
theorem joint_advanced_head_section_nonspecial : ¬ IsSpecial Sec B q := by
  intro hSp
  rcases hSp with hzero | ⟨_, hMem⟩
  · exact (by decide : (1 : ℕ) ≠ 0) (Sec_level.symm.trans hzero.1)
  have hE : origMembers Sec B = [D' 0, D' 1] := rfl
  rw [Sec_bar, hE] at hMem
  have hLocal := (mem_memberInterLocus_iff.mp hMem).2
  have hne : ∃ᶠ a : ℂ in 𝓝 0, a ≠ 0 := by
    have hF : ∃ᶠ a : ℂ in 𝓝[≠] 0, True :=
      Filter.Eventually.frequently (Filter.Eventually.of_forall fun _ => trivial)
    exact ((frequently_nhdsWithin_iff).mp hF).mono (fun _ ha => ha.2)
  obtain ⟨a, ha, hA⟩ := (hne.and_eventually (axis_near.eventually hLocal)).exists
  obtain ⟨haV, haD, haS, hau⟩ := axis_geometry a ha
  have hzSec : axis a ∈ (geoTransformAlong Sec B).cosupp := by
    apply hA haS
    intro H hH hqH
    rcases List.mem_cons.mp hH with rfl | hH
    · exact haD
    · rw [List.mem_singleton] at hH
      exact (q_not_D1 (hH ▸ hqH)).elim
  exact ha (hau.symm.trans (proper_cosupp_middle_zero haV (Sec_cosupp_eq.symm ▸ hzSec)))

private theorem split_zero {n : ℕ} {X Y : CMfd.{0} n} (T : BlowupTower X Y) :
    split T 0 = ⟨Y, T, BlowupTower.refl (X := Y)⟩ := by
  cases T <;> rfl

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
/-- The literal native lift takes the finite branch. Its next letter is
the actual order-zero monomial value on the restarted selected mask. -/
theorem joint_advanced_head_exact_native_monomial_read :
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ x ∈ V, RegularAtDim (n := 3) V x 2)
      (N : BlowupTower Z (nativeManifold (Nat.le_succ 2) V hV))
      (z : nativeManifold (Nat.le_succ 2) V hV),
      Lift (Nat.le_succ 2) (zeroPlane U) plane_closed (zeroPlane_regular U)
        Sec.E B V hVc hV N ∧
      N.length = 1 ∧ z.val = q ∧ z ∈ (geoTransformAlong N₀ N).cosupp ∧
      IsCanonical N₀ (Seq.StepOneValueMasked.stepOneInvM R N₀) N ∧
      ¬ IsSpecial N₀ N z ∧ regimeRun (stepRegime N₀ 1) N z = 0 ∧
      ∃ hz : z ∈ maskA N₀ N z,
        let O := maskA N₀ N z
        let J := lowerMarkedM N₀ 1 N z
        let p : O := ⟨z, hz⟩
        nmOrd (M := CMfd.of (n := 2) O) J p = 0 ∧
        Seq.StepOneValueMasked.stepOneInvM R N₀ N z =
          toLex (1, (↑(show ValTy 1 from toLex
            (0, toLex (Sum.inl (gammaAlong 2 J.N J.ideal J.E J.d p)))) : WithTop (ValTy 1))) := by
  obtain ⟨V, hVc, hV, N, z, hLift, hlen, hzval, hzCos, hCan, hBranch⟩ :=
    joint_advanced_head_literal_native_discrepancy
  have hChron := actual_section_step_one_chronology U Q.N native_source_domain.isWellFormed.isClosedSubmanifold_N
    Q.E native_source_domain.isWellFormed.isSNCDivisor Sec.ideal Sec_domain.isWellFormed.isCoherent Q.d
    (T := B) (V := V) (Q := N) hLift
  have hNS : ¬ IsSpecial N₀ N z := by
    intro h
    have hS := (hChron.2.2.1 z).2.mpr h
    change IsSpecial Sec B z.val at hS
    rw [hzval] at hS
    exact joint_advanced_head_section_nonspecial hS
  have hLevel : level N₀ N z = 1 := by
    have h := (hChron.2.2.1 z).1
    change level Sec B z.val = level N₀ N z at h
    rw [hzval, Sec_level] at h
    exact h.symm
  have hRun : regimeRun (stepRegime N₀ 1) N z = 0 := by
    have hLe := (positive_normal_section_run Q native_source_domain (s := 0) B upper_test q).1
    have hClock := hChron.2.2.2.2 1 z
    change regimeRun (stepRegime Sec 1) B z.val = regimeRun (stepRegime N₀ 1) N z at hClock
    rw [hzval] at hClock
    have hR := joint_added_boundary_upper_regime_advances.2.2
    rw [joint_added_boundary_upper_regime_advances.2.1] at hR
    exact Nat.eq_zero_of_le_zero (hClock ▸ hR ▸ hLe)
  let A := nativeManifold (Nat.le_succ 2) V hV
  have hTrans : IsTransverse 3 (zeroPlane U) Sec.E :=
    isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor native_source_domain.isWellFormed.isSNCDivisor)
  have hSupport : Sec.N ⊆ zeroPlane U := fun _ hx => ⟨mem_univ _, hx.2⟩
  have hDom : IsInvDomain 2 N₀ :=
    isInvDomain_nativePullback (by decide : 0 < 3) (Nat.le_succ 2) (zeroPlane_regular U)
      Sec Sec_domain hSupport hTrans
  have hTest := HironakaActualNativeSectionNormalCrossings.Lift.native_test hLift
    (by decide : 0 < 3) Sec_domain.isWellFormed.isSNCDivisor hTrans Sec rfl hSupport
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem Sec_domain.isWellFormed.isCoherent hg) Sec_test
  have hBarTest := ((bar_local_any_boundary (X := Z) N₀ hDom).wEquiv.2 N).1.mp hTest
  have hz : z ∈ maskA N₀ N z := mem_maskA N₀ hDom.isWellFormed hDom.one_le_d
    (by decide) N hBarTest hLevel.ge hNS
  let O := maskA N₀ N z
  let J := lowerMarkedM N₀ 1 N z
  let S := CMfd.of (n := 2) O
  let T : BlowupTower S S := .refl
  let p : O := ⟨z, hz⟩
  let v := R.inv J T p
  have hRead : Seq.StepOneValueMasked.stepOneInvM R N₀ N z =
      toLex (1, (v : WithTop (ValTy 1))) := by
    change Seq.StepOneValueMasked.stepOneInvL R N₀ (lowerMarkedM N₀) N z = _
    rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R N₀ (lowerMarkedM N₀) N hNS, hLevel, hRun]
    have hSplit : split N 0 = ⟨A, N, BlowupTower.refl (X := A)⟩ := split_zero N
    simp only [head, tail]
    erw [hSplit]
    change toLex (1, Seq.StepOneValueMasked.lowerValueL R N₀ (lowerMarkedM N₀) 1 N
      (BlowupTower.refl (X := A)) z) = _
    unfold Seq.StepOneValueMasked.lowerValueL
    erw [dif_pos (show (BlowupTower.refl (X := A)).proj z ∈
      lowerMask N₀ 1 N ((BlowupTower.refl (X := A)).proj z) from hz)]
    rfl
  have hFirst : fstEntry v = 0 := by
    rcases hBranch with hTop | ⟨w, hw, hVal⟩
    · have he := congrArg (fun x : ℕ ×ₗ WithTop (ValTy 1) => (ofLex x).2) (hRead.symm.trans hTop)
      exact (WithTop.coe_ne_top he).elim
    · have he := congrArg (fun x : ℕ ×ₗ WithTop (ValTy 1) => (ofLex x).2) (hRead.symm.trans hVal)
      exact (congrArg (fstEntry (k := 0)) (WithTop.coe_injective he)).trans hw
  have hOrder : nmOrd (M := S) J p = 0 := hFirst
  have hVal : v = toLex (0, toLex (Sum.inl (gammaAlong 2 J.N J.ideal J.E J.d p))) := by
    let F : ∀ {A : CMfd.{0} 2}, MarkedIdeal 2 A →
        ∀ {B : CMfd.{0} 2}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy 0) :=
      fun {A} M {B} T z => Seq.StepOneValueMasked.stepOneInvM (X := A)
        (invFamily (by decide : 0 < 2) 0) M (Y := B) T z
    change genInv F J T p = _
    exact genInv_of_nmOrd_eq_zero F J T (show nmOrd (geoTransformAlong J T) p = 0 from hOrder)
  refine ⟨V, hVc, hV, N, z, hLift, hlen, hzval, hzCos, hCan, hNS, hRun, hz, hOrder, ?_⟩
  exact hRead.trans (congrArg (fun w : ValTy 1 => toLex (1, (w : WithTop (ValTy 1)))) hVal)

private def coordinateChart (j : Fin 3) : FlatChart 3 C :=
  { yChart with j := j, hj := Nat.zero_le _ }

private theorem chart_domain_all (j : Fin 3) (x : X) : x ∈ (coordinateChart j).dom := by
  change x ∈ (chartAt (ComplexModel 3) p).source ∩ _
  refine ⟨?_, mem_univ _⟩
  rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source]
  exact mem_univ _

private theorem coordinateChart_cover (z : Y) : ∃ j, z ∈ (coordinateChart j).source := by
  classical
  by_contra! h
  have hZero (j : Fin 3) : extVal (yChart.τ j) z = 0 := by
    by_contra hNZ
    exact h j ((coordinateChart j).mem_source_iff.mpr ⟨chart_domain_all j _, hNZ⟩)
  by_cases hz : z.base ∈ C
  · apply BlowupSpace.dirVec_not_mem hz
    rw [BlowupSpaceTangent.mem_tangentSpace_iff yChart.hsrc yChart.hflat (chart_domain_all 1 _) hz]
    intro i _
    exact (extVal_of_mem hz).symm.trans (hZero i)
  · apply hz
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    have hp : p.val = 0 := map_zero (tangentInclusion 2 1)
    rw [hp]
    ext i
    exact (extVal_of_not_mem hz).symm.trans (hZero i)

private theorem linear_member (j : Fin 3) (hj : j ≠ 1) (z : X) :
    M.ideal.mem z (fun w : X => w.val j) := by
  have he : j = 0 ∨ j = 2 := by fin_cases j <;> simp_all
  obtain rfl | rfl := he
  · change P.ideal.mem z (paddedGenerator (.inl true) ∘ (Subtype.val : X → ComplexModel 3))
    rw [proper_source_generators]
    have hHol : HolomorphicAt 3 (paddedGenerator (.inl true)) z.val :=
      Eventually.of_forall fun w => paddedGenerator_hol (.inl true) w
    exact GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨paddedGenerator (.inl true), isInSpanAt_self ⟨.inl true, rfl⟩ hHol, rfl⟩
        (hHol.comp_contMDiff (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)))
  · change P.ideal.mem z (paddedGenerator (.inr ()) ∘ (Subtype.val : X → ComplexModel 3))
    rw [proper_source_generators]
    have hHol : HolomorphicAt 3 (paddedGenerator (.inr ())) z.val :=
      Eventually.of_forall fun w => paddedGenerator_hol (.inr ()) w
    exact GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨paddedGenerator (.inr ()), isInSpanAt_self ⟨.inr (), rfl⟩ hHol, rfl⟩
        (hHol.comp_contMDiff (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)))

set_option backward.isDefEq.respectTransparency false in
private theorem linear_pivot_not_cosupp {j : Fin 3} (hj : j ≠ 1) {z : Y}
    (hz : z ∈ (coordinateChart j).source) : z ∉ (geoTransformAlong M B).cosupp := by
  let c := coordinateChart j
  intro hCos
  have hMem : (geoTransformAlong M B).ideal.mem z (fun _ => 1) := by
    change (M.geoTransform C π).ideal.mem z _
    rw [geoTransform_ideal_eq_controlledTransform (𝔪 := M) (show M.N = univ from preimage_univ)
      joint_added_boundary_test.1.isWellFormed.isCoherent hπ]
    refine mem_colon_iff.mpr ⟨holomorphicAt_const 1, ?_⟩
    intro g hg
    rw [show M.d = 1 from rfl, idealPow_one_exceptionalDivisor hπ] at hg
    change (GermIdeal.pullback (m := 3) π (vanishingIdeal (n := 3) C)).mem z g at hg
    change (GermIdeal.pullback (m := 3) π M.ideal).mem z (g * 1)
    rw [mul_one]
    apply GermIdeal.mem_pullback_iff.mpr
    refine IsInSpanAt.mono (S := fun t : Y → ℂ => t = c.τ j ∘ π) ?_
      (IsInSpanAt.of_forall_eq_mul (h := c.τ j ∘ π) ?_ (GermIdeal.mem_pullback_iff.mp hg))
    · intro t ht
      subst t
      exact ⟨c.τ j, linear_member j hj (π z), rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, _, hbh, hbeq⟩ := exists_eq_sum_flatCoord c.Φ c.hsrc c.hflat hz.1 ha
      let d := fun (i : Fin 3) (w : Y) => if i = j then 1 else c.toFun w i
      refine ⟨fun w => ∑ i, b i (π w) * d i w, ?_, ?_⟩
      · refine HolomorphicAt.sum _ fun i _ => (holomorphicAt_comp_blowupProj (hbh i)).mul ?_
        by_cases hi : i = j
        · simpa [d, hi] using (holomorphicAt_const (n := 3) (x := z) (1 : ℂ))
        · simpa [d, hi] using c.holomorphicAt_coord hz i
      · filter_upwards [hπ.contMDiff.continuous.continuousAt.eventually hbeq,
          c.isOpen_source.mem_nhds hz] with w hw hwV
        have he : c.τ j (π w) = c.toFun w j := (c.τ_base_eq hwV c.j).trans (c.monomial_apply_j _)
        change a (π w) = (∑ i, b i (π w) * d i w) * c.τ j (π w)
        rw [hw, Finset.sum_mul, he]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hi := c.τ_base_eq hwV i
        change c.τ i (π w) = monomial 0 j (c.toFun w) i at hi
        change b i (π w) * c.τ i (π w) = _
        rw [hi, monomial_apply]
        by_cases h : i = j
        · subst i
          simp [d]
        · simp [d, h, mul_assoc]
  exact one_ne_zero ((vanishesToOrderOn_one_iff hCos.1 (holomorphicAt_const (1 : ℂ))).mp
    (hCos.2 _ hMem))

set_option backward.isDefEq.respectTransparency false in
private theorem middle_cosupp_x_zero {z : Y} (hz : z ∈ chartOpen)
    (hCos : z ∈ (geoTransformAlong M B).cosupp) : yChart.toFun z (0 : Fin 3) = 0 := by
  have hMem : (geoTransformAlong M B).ideal.mem z (fun w => yChart.toFun w (0 : Fin 3)) := by
    change (M.geoTransform C π).ideal.mem z _
    rw [geoTransform_ideal_eq_controlledTransform (𝔪 := M) (show M.N = univ from preimage_univ)
      joint_added_boundary_test.1.isWellFormed.isCoherent hπ]
    change (controlledTransform hπ M.ideal 1).mem z _
    refine mem_controlledTransform_of_eq_pow_mul equation_on_chart hz (linear_member 0 (by decide) (π z))
      (yChart.holomorphicAt_coord hz 0) ?_
    filter_upwards [chartOpen.isOpen.mem_nhds hz] with w hw
    change (π w).val (0 : Fin 3) = exceptionalCoordinate w ^ 1 * yChart.toFun w (0 : Fin 3)
    rw [chart_projection w hw, monomial_apply, exceptionalCoordinate_coord w hw]
    simp [mul_comm]
  exact (vanishesToOrderOn_one_iff hCos.1 (yChart.holomorphicAt_coord hz 0)).mp (hCos.2 _ hMem)

/-- The endpoint cosupport of the padded example is the single surviving
middle-chart origin, globally across all three projective charts. -/
theorem joint_advanced_head_endpoint_cosupport :
    (geoTransformAlong M B).cosupp = {q} := by
  ext z
  constructor
  · intro hCos
    obtain ⟨j, hj⟩ := coordinateChart_cover z
    have h1 : j = 1 := by
      by_contra hh
      exact linear_pivot_not_cosupp hh hj hCos
    subst j
    have hz : z ∈ chartOpen := hj
    have hz0 := middle_cosupp_x_zero hz hCos
    have hz1 := proper_cosupp_middle_zero hz hCos
    have hz2 : yChart.toFun z (2 : Fin 3) = 0 := by
      have hMem : (geoTransformAlong M B).ideal.mem z (fun w => yChart.toFun w (2 : Fin 3)) := by
        change (M.geoTransform C π).ideal.mem z _
        rw [geoTransform_ideal_eq_controlledTransform (𝔪 := M) (show M.N = univ from preimage_univ)
          joint_added_boundary_test.1.isWellFormed.isCoherent hπ]
        exact normal_generator z hz
      exact (vanishesToOrderOn_one_iff hCos.1 (yChart.holomorphicAt_coord hz 2)).mp (hCos.2 _ hMem)
    apply mem_singleton_iff.mpr
    apply yChart.toPartialEquiv.injOn hz chart_q.1
    change yChart.toFun z = yChart.toFun q
    rw [chart_q.2]
    ext i
    fin_cases i
    · exact hz0
    · exact hz1
    · exact hz2
  · intro hz
    rw [mem_singleton_iff.mp hz]
    exact joint_added_boundary_survives_nonspecial.1

private theorem maxLocus_singleton {X Λ : Type} [LinearOrder Λ] (v : X → Λ) (x : X) :
    ResolutionDriver.maxLocus v {x} = {x} := by
  ext y
  constructor
  · exact fun hy => hy.1
  · intro hy
    refine ⟨hy, ?_⟩
    intro z hz
    rw [mem_singleton_iff.mp hz, mem_singleton_iff.mp hy]

set_option maxHeartbeats 850000 in
set_option backward.isDefEq.respectTransparency false in
/-- The full original upper endpoint maxima are singletons on the actual
common lift. Their underlying points agree despite the different raw values. -/
theorem joint_advanced_head_full_max_loci :
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ x ∈ V, RegularAtDim (n := 3) V x 2)
      (N : BlowupTower Z (nativeManifold (Nat.le_succ 2) V hV))
      (z : nativeManifold (Nat.le_succ 2) V hV),
      Lift (Nat.le_succ 2) (zeroPlane U) plane_closed (zeroPlane_regular U)
        Sec.E B V hVc hV N ∧ z.val = q ∧
      ResolutionDriver.maxLocus
        (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) M B)
        (geoTransformAlong M B).cosupp = {q} ∧
      ResolutionDriver.maxLocus (Seq.StepOneValueMasked.stepOneInvM R N₀ N)
        (geoTransformAlong N₀ N).cosupp = {z} := by
  obtain ⟨V, hVc, hV, N, z, hLift, _, hq, _, _, _, _, _, _, _⟩ :=
    joint_advanced_head_exact_native_monomial_read
  have hTrans : IsTransverse 3 (zeroPlane U) Sec.E :=
    isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor native_source_domain.isWellFormed.isSNCDivisor)
  have hSupport : Sec.N ⊆ zeroPlane U := fun _ hx => ⟨mem_univ _, hx.2⟩
  have hNative := HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift
    (by decide : 0 < 3) Sec_domain.isWellFormed.isSNCDivisor hTrans Sec rfl hSupport
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem Sec_domain.isWellFormed.isCoherent hg)
  have hN : (geoTransformAlong N₀ N).cosupp = {z} := by
    rw [hNative, ← Sec_cosupp_eq, joint_advanced_head_endpoint_cosupport]
    ext w
    change w.val ∈ ({q} : Set Y) ↔ w ∈ {z}
    rw [mem_singleton_iff, mem_singleton_iff, ← hq]
    exact ⟨Subtype.ext, congrArg Subtype.val⟩
  refine ⟨V, hVc, hV, N, z, hLift, hq, ?_, ?_⟩
  · rw [joint_advanced_head_endpoint_cosupport, maxLocus_singleton]
  · rw [hN, maxLocus_singleton]

end
end Hironaka.HironakaG1LaterAdvancedHeadNativeValueExample
