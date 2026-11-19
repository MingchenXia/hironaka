import Hironaka.Resolution.HironakaG1LaterAdvancedHeadNativePayloadExample
import Hironaka.Blowup.BlowupExistence
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

/-! The closing point blowup of the actual canonical advanced-head history. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterAdvancedHeadTerminalExample

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
  HironakaG1LaterAdvancedHeadNativePayloadExample
  BlowupExistence BlowupExistenceOriginIdeal TransformOffCentre
  HironakaOneDimensionalCanonicalSuperlevels DerivativeIdeal GermIdealTotalTransform

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


private abbrev M₁ := geoTransformAlong M B
private abbrev RP := invFamily (by decide : 0 < 3) 2
private abbrev C₁ : Set Y := {q}
private abbrev c (j : Fin 3) (z : Y) : ℂ := yChart.toFun z j
private abbrev chartOpen : Opens Y := ⟨yChart.source, yChart.isOpen_source⟩

private theorem source_member (j : Bool ⊕ Unit) (z : X) :
    M.ideal.mem z (paddedGenerator j ∘ (Subtype.val : X → ComplexModel 3)) := by
  change P.ideal.mem z _
  rw [proper_source_generators]
  have hHol : HolomorphicAt 3 (paddedGenerator j) z.val :=
    Eventually.of_forall fun w => paddedGenerator_hol j w
  exact GermIdeal.mem_pullback_iff.mpr
    (isInSpanAt_self ⟨paddedGenerator j, isInSpanAt_self ⟨j, rfl⟩ hHol, rfl⟩
      (hHol.comp_contMDiff (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)))

private theorem chart_generators (j : Fin 3) {z : Y} (hz : z ∈ chartOpen) :
    M₁.ideal.mem z (c j) := by
  change (M.geoTransform C π).ideal.mem z _
  rw [geoTransform_ideal_eq_controlledTransform (𝔪 := M) (show M.N = univ from preimage_univ)
    joint_added_boundary_test.1.isWellFormed.isCoherent hπ]
  fin_cases j
  · refine mem_controlledTransform_of_eq_pow_mul equation_on_chart hz (source_member (.inl true) (π z))
      (yChart.holomorphicAt_coord hz 0) ?_
    filter_upwards [chartOpen.isOpen.mem_nhds hz] with w hw
    change (π w).val (0 : Fin 3) = exceptionalCoordinate w ^ 1 * yChart.toFun w (0 : Fin 3)
    rw [chart_projection w hw, monomial_apply, exceptionalCoordinate_coord w hw]
    simp [mul_comm]
  · refine mem_controlledTransform_of_eq_pow_mul equation_on_chart hz (source_member (.inl false) (π z))
      (yChart.holomorphicAt_coord hz 1) ?_
    filter_upwards [chartOpen.isOpen.mem_nhds hz] with w hw
    change ((π w).val (1 : Fin 3)) ^ 2 = exceptionalCoordinate w ^ 1 * yChart.toFun w (1 : Fin 3)
    rw [chart_projection w hw, monomial_apply, exceptionalCoordinate_coord w hw]
    simp [pow_two]
  · exact normal_generator z hz

private def chart : ComplexChart 3 Y :=
  ⟨yChart.homeo, atlasHomeo_mem_atlas yChart.toPartialEquiv (Or.inl ⟨yChart, rfl⟩)⟩

private theorem chart_zero : chart.val q = 0 := chart_q.2
private theorem chart_source : q ∈ chart.val.source := chart_q.1
private theorem chart_inv_zero : chart.val.symm 0 = q := by
  rw [← chart_zero, chart.val.left_inv chart_source]

private theorem stage_wf : M₁.IsWellFormed :=
  MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    joint_added_boundary_test.1.isWellFormed B joint_added_boundary_test.2

set_option backward.isDefEq.respectTransparency false in
private theorem point_stalk_le {g : Y → ℂ} (hg : (vanishingIdeal (n := 3) C₁).mem q g) :
    M₁.ideal.mem q g := by
  let f : ComplexModel 3 → ℂ := g ∘ chart.val.symm
  have hfHol : HolomorphicAt 3 f 0 := by
    have h := eventually_differentiableAt_comp_symm chart chart_source hg.1
    rw [chart_zero] at h
    exact h.mono fun _ h => h.mdifferentiableAt
  have hf : (vanishingIdeal (n := 3) ({0} : Set (ComplexModel 3))).mem 0 f := by
    refine ⟨hfHol, Eventually.of_forall fun w hw => ?_⟩
    rw [mem_singleton_iff.mp hw]
    change g (chart.val.symm 0) = 0
    rw [chart_inv_zero]
    exact hg.2.self_of_nhds (mem_singleton _)
  obtain ⟨H, hH, hEq⟩ := exists_eq_sum_coordFun hf
  have hq : Tendsto (chart.val : Y → ComplexModel 3) (𝓝 q) (𝓝 0) := by
    rw [← chart_zero]
    exact (chart.val.continuousAt chart_source).tendsto
  have hHG (i : Fin 3) : HolomorphicAt 3 (H i ∘ chart.val) q := by
    apply holomorphicAt_comp_chart chart chart_source
    rw [chart_zero]
    exact (hH i).mono fun _ h => mdifferentiableAt_iff_differentiableAt.mp h
  apply mem_of_isInSpanAt_mem stage_wf.isCoherent
  refine ⟨hg.1, 3, c, fun i => H i ∘ chart.val, fun i => chart_generators i chart_q.1,
    hHG, ?_⟩
  filter_upwards [hq.eventually hEq, chart.val.open_source.mem_nhds chart_source] with z he hz
  change g (chart.val.symm (chart.val z)) = _ at he
  rw [chart.val.left_inv hz] at he
  change g z = ∑ i : Fin 3, c i z * H i (chart.val z) at he
  simpa only [Function.comp_apply, mul_comm] using he

private theorem C₁_smooth : IsClosedSubmanifold 3 C₁ :=
  (PointSupportedIdealPrincipalization.singleton_geometry_and_coherence (n := 3) q).1

private theorem C₁_thin : interior C₁ = ∅ := by
  by_contra hn
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hn
  have hzq : z = q := mem_singleton_iff.mp (interior_subset hz)
  subst z
  have hN : C₁ ∈ 𝓝 q := mem_interior_iff_mem_nhds.mp hz
  have hI := chart.val.image_mem_nhds chart_source hN
  have hImage : chart.val '' C₁ = ({0} : Set (ComplexModel 3)) := by
    rw [show C₁ = {q} from rfl, image_singleton, chart_zero]
  rw [hImage] at hI
  obtain ⟨v, hv, hnz⟩ := exists_coord_ne_zero_of_mem_nhds hI (0 : Fin 3)
  rw [mem_singleton_iff.mp hv] at hnz
  exact hnz rfl

set_option maxHeartbeats 750000 in
set_option backward.isDefEq.respectTransparency false in
private theorem resolve_stage {A : CMfd.{0} 3} {F : Set Y} (hf : F = C₁)
    (ρ : A → Y) (hρ : IsBlowupAlong 3 F ρ) : (M₁.geoTransform F ρ).cosupp = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hSub : F ⊆ M₁.cosupp := by rw [hf, joint_advanced_head_endpoint_cosupport]
  have hP := cosupp_geoTransform_subset_preimage M₁ stage_wf.isClosedSubmanifold_N.1
    (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem stage_wf.isCoherent h) hρ hSub hz
  have hq : ρ z = q := by
    change ρ z ∈ M₁.cosupp at hP
    rw [joint_advanced_head_endpoint_cosupport] at hP
    exact mem_singleton_iff.mp hP
  have hN : M₁.N = univ := by
    change geoStrictTransform π C M.N = univ
    rw [show M.N = univ from preimage_univ, geoStrictTransform_univ hπ]
  have hU : (M₁.geoTransform F ρ).ideal.mem z (fun _ => 1) := by
    rw [geoTransform_ideal_eq_controlledTransform (𝔪 := M₁) hN stage_wf.isCoherent hρ]
    change (controlledTransform hρ M₁.ideal 1).mem z _
    refine mem_colon_iff.mpr ⟨holomorphicAt_const 1, ?_⟩
    intro g hg
    rw [idealPow_one_exceptionalDivisor hρ] at hg
    change (GermIdeal.pullback (m := 3) ρ (vanishingIdeal (n := 3) F)).mem z g at hg
    change (GermIdeal.pullback (m := 3) ρ M₁.ideal).mem z (g * 1)
    rw [mul_one]
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hg))
    rintro a ⟨s, hs, rfl⟩
    refine ⟨s, ?_, rfl⟩
    rw [hq]
    rw [hf, hq] at hs
    exact point_stalk_le hs
  have hg := hz.2 _ hU
  exact one_ne_zero ((vanishesToOrderOn_one_iff hz.1 (holomorphicAt_const (1 : ℂ))).mp hg)

private abbrev padded0 : ℕ ×ₗ WithTop (ValTy 2) :=
  toLex (2, (↑(positiveSuccessorRead 1 (toLex (0, (⊤ : WithTop (ValTy 1))))) : WithTop (ValTy 2)))

private abbrev padded1 : ℕ ×ₗ WithTop (ValTy 2) :=
  toLex (1, (positiveSuccessorRead 1
    (toLex (1, (↑(positiveSuccessorRead 1 (toLex (0, (⊤ : WithTop (ValTy 0))))) :
      WithTop (ValTy 1)))) : WithTop (ValTy 2)))

private theorem padded_first_letters :
    (∀ y ∈ M.cosupp, y = p ∧ Seq.StepOneValueMasked.stepOneInvM RP M T y = padded0) ∧
      (∀ y ∈ M₁.cosupp, y = q ∧ Seq.StepOneValueMasked.stepOneInvM RP M B y = padded1) := by
  constructor
  · intro y hy
    have he : y = p := by
      have hc : M.cosupp = ({p} : Set X) := joint_advanced_initial_cosupport
      rw [hc] at hy
      exact mem_singleton_iff.mp hy
    exact ⟨he, by rw [he]; exact joint_advanced_head_initial_exact_comparison.2⟩
  · intro y hy
    have he : y = q := mem_singleton_iff.mp (joint_advanced_head_endpoint_cosupport ▸ hy)
    exact ⟨he, by rw [he]; exact joint_advanced_head_exact_upper_value⟩

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
/-- The two attained padded letters exhaust the cosupport along the
canonical two-step history. The closing blowup resolves the example. -/
theorem joint_advanced_head_padded_complete_history :
    ∃ (A : CMfd.{0} 3) (ρ : A → Y) (hρ : IsBlowupAlong 3 C₁ ρ),
      let H : BlowupTower X A := .step B C₁ ρ hρ
      IsGeoTestTower M H ∧ IsCanonical M (Seq.StepOneValueMasked.stepOneInvM RP M) H ∧
      (∀ y ∈ M.cosupp, y = p ∧ Seq.StepOneValueMasked.stepOneInvM RP M T y = padded0) ∧
      (∀ y ∈ M₁.cosupp, y = q ∧ Seq.StepOneValueMasked.stepOneInvM RP M B y = padded1) ∧
      (geoTransformAlong M H).cosupp = ∅ := by
  obtain ⟨A, hA, hC, hM, ρ, hρ⟩ := exists_isBlowupAlong C₁ C₁_smooth C₁_thin
  let W := CMfd.of (n := 3) A
  have hTest : IsGeoTestTower M (.step B C₁ ρ hρ : BlowupTower X W) := by
    refine ⟨joint_added_boundary_test.2, C₁_smooth, ?_,
      hasNormalCrossings_singleton q stage_wf.isSNCDivisor⟩
    rw [joint_advanced_head_endpoint_cosupport]
  have hCan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM RP M)
      (.step B C₁ ρ hρ : BlowupTower X W) := by
    refine ⟨joint_advanced_head_isCanonical _, Or.inr ?_⟩
    rw [joint_advanced_head_endpoint_cosupport, maxLocus_singleton]
  exact ⟨W, ρ, hρ, hTest, hCan, padded_first_letters.1, padded_first_letters.2, resolve_stage (A := W) rfl ρ hρ⟩

private theorem singleton_thin {n : ℕ} {A : CMfd.{0} (n+1)} (z : A) :
    interior ({z} : Set A) = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro y hy
  have hyz : y = z := mem_singleton_iff.mp (interior_subset hy)
  subst y
  have ho : IsOpen ({z} : Set A) := by
    apply isOpen_iff_mem_nhds.mpr
    intro w hw
    rw [mem_singleton_iff.mp hw]
    exact mem_interior_iff_mem_nhds.mp hy
  let e := (complexChartAt (n := n+1) z).val
  have hi := e.isOpen_image_of_subset_source ho (singleton_subset_iff.mpr (mem_complexChartAt_source z))
  rw [image_singleton] at hi
  exact not_isOpen_singleton (e z) hi

private abbrev native0 : ℕ ×ₗ WithTop (ValTy 1) := toLex (2, (⊤ : WithTop (ValTy 1)))
private abbrev bornGamma : WithBot MonomialInvariant.Val :=
  ↑(toLex (1, toLex (1, toColex ({1} : Finset ℕ))))
private abbrev native1 : ℕ ×ₗ WithTop (ValTy 1) :=
  toLex (1, (↑(show ValTy 1 from toLex (0, toLex (Sum.inl bornGamma))) : WithTop (ValTy 1)))

private abbrev pN : Z := ⟨p, ⟨mem_univ _, HironakaActualCentreJointJets.actualJointNormalProjection_tangent 2 1 0⟩⟩
private abbrev Nrefl : BlowupTower Z Z := .refl

set_option maxHeartbeats 2500000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual common lift extends across the closing canonical centre.
The listed letters exhaust both full histories up to the empty cosupport. -/
theorem joint_advanced_head_common_complete_history :
    ∃ (V : Set Y) (hVc : IsClosed V)
      (hV : ∀ x ∈ V, RegularAtDim (n := 3) V x 2)
      (N : BlowupTower Z (nativeManifold (Nat.le_succ 2) V hV))
      (z : nativeManifold (Nat.le_succ 2) V hV)
      (A : CMfd.{0} 3) (ρ : A → Y) (C₂ : Set Y) (hρ : IsBlowupAlong 3 C₂ ρ)
      (W : Set A) (hWc : IsClosed W)
      (hW : ∀ x ∈ W, RegularAtDim (n := 3) W x 2)
      (N₂ : BlowupTower Z (nativeManifold (Nat.le_succ 2) W hW)),
      let H : BlowupTower X A := .step B C₂ ρ hρ
      C₂ = {q} ∧
      Lift (Nat.le_succ 2) (zeroPlane U) plane_closed (zeroPlane_regular U) Sec.E B V hVc hV N ∧
      Lift (Nat.le_succ 2) (zeroPlane U) plane_closed (zeroPlane_regular U) Sec.E H W hWc hW N₂ ∧
      (∃ (ρₙ : nativeManifold (Nat.le_succ 2) W hW → nativeManifold (Nat.le_succ 2) V hV)
        (hρₙ : IsBlowupAlong 2 ({z} : Set (nativeManifold (Nat.le_succ 2) V hV)) ρₙ),
        N₂ = .step N {z} ρₙ hρₙ) ∧
      IsCanonical M (Seq.StepOneValueMasked.stepOneInvM RP M) H ∧
      IsCanonical N₀ (Seq.StepOneValueMasked.stepOneInvM R N₀) N₂ ∧
      (M.cosupp = {p} ∧ Seq.StepOneValueMasked.stepOneInvM RP M T p = padded0) ∧
      (N₀.cosupp = {pN} ∧ Seq.StepOneValueMasked.stepOneInvM R N₀ Nrefl pN = native0) ∧
      (M₁.cosupp = {q} ∧ Seq.StepOneValueMasked.stepOneInvM RP M B q = padded1) ∧
      ((geoTransformAlong N₀ N).cosupp = {z} ∧ z.val = q ∧
        Seq.StepOneValueMasked.stepOneInvM R N₀ N z = native1) ∧
      (geoTransformAlong M H).cosupp = ∅ ∧ (geoTransformAlong N₀ N₂).cosupp = ∅ := by
  obtain ⟨V, hVc, hV, N, z, hLift, _, hq, hCanN, hValN⟩ :=
    joint_advanced_head_native_numerical_payload
  let Vₙ := nativeManifold (Nat.le_succ 2) V hV
  let D : Set Vₙ := {z}
  let C₂ : Set Y := (Subtype.val : V → Y) '' D
  have hC₂ : C₂ = C₁ := by
    change (Subtype.val : V → Y) '' {z} = {q}
    rw [image_singleton, hq]
  have hSmooth : IsClosedSubmanifold 3 C₂ := hC₂.symm ▸ C₁_smooth
  have hThin : interior C₂ = ∅ := by rw [hC₂]; exact C₁_thin
  obtain ⟨AA, _, _, _, ρ, hρ⟩ := exists_isBlowupAlong C₂ hSmooth hThin
  let A := CMfd.of (n := 3) AA
  let H : BlowupTower X A := .step B C₂ ρ hρ
  have hD : IsClosedSubmanifold 2 D :=
    (PointSupportedIdealPrincipalization.singleton_geometry_and_coherence (n := 2) z).1
  have hDThin : interior D = ∅ := singleton_thin (A := Vₙ) z
  let W : Set A := geoStrictTransform ρ C₂ V
  let hW : ∀ x ∈ W, RegularAtDim (n := 3) W x 2 := strictRegular (Z := A) hVc hV D ρ hρ
  let ρₙ := nativeProjection (Nat.le_succ 2) (Z := A) hVc hV D ρ hρ
  let hρₙ := nativeProjection_genuine (Nat.le_succ 2) (Z := A) hVc hV D hD hDThin ρ hρ
  let N₂ : BlowupTower Z (nativeManifold (Nat.le_succ 2) W hW) := .step N D ρₙ hρₙ
  have hQ : IsInvDomain 2 Q := Q_domain
  have hSec : IsInvDomain 2 Sec := section_projected_domain _ Q.N Q.E Q.ideal Q.d hQ
  have hLoc := properNormalMarked_locWPEquiv_section Q hQ
  have hTest1 : IsGeoTestTower M B := joint_added_boundary_test.2
  have hTestSec1 := (hLoc.wEquiv.2 B).1.mp hTest1
  have hSec1 : (geoTransformAlong Sec B).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hSec.isWellFormed B hTestSec1
  have hNC : HasNormalCrossings 3 C₂ (boundary Sec.E B) := by
    rw [hC₂]
    change HasNormalCrossings 3 {q} (geoTransformAlong Sec B).E
    exact hasNormalCrossings_singleton q hSec1.isSNCDivisor
  have hLift₂ : Lift (Nat.le_succ 2) (zeroPlane U) plane_closed (zeroPlane_regular U)
      Sec.E H W isClosed_closure hW N₂ :=
    Lift.step (Z := A) hLift D hD hDThin ρ hρ hNC
  have hPtest : IsGeoTestTower M H := by
    refine ⟨hTest1, hSmooth, ?_, ?_⟩
    · rw [hC₂, joint_advanced_head_endpoint_cosupport]
    · rw [hC₂]
      exact hasNormalCrossings_singleton q stage_wf.isSNCDivisor
  have hPcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM RP M) H := by
    refine ⟨joint_advanced_head_isCanonical _, Or.inr ?_⟩
    rw [hC₂, joint_advanced_head_endpoint_cosupport, maxLocus_singleton]
  have hTrans : IsTransverse 3 (zeroPlane U) Sec.E :=
    isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hSupport : Sec.N ⊆ zeroPlane U := fun _ hx => ⟨mem_univ _, hx.2⟩
  have hHol (x : X) (g : X → ℂ) (hg : Sec.ideal.mem x g) : HolomorphicAt 3 g x :=
    GermIdeal.IsCoherent.holomorphicAt_mem hSec.isWellFormed.isCoherent hg
  have hTransfer₁ := HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift
    (by decide : 0 < 3) hSec.isWellFormed.isSNCDivisor hTrans Sec rfl hSupport hHol
  have hTransfer₂ := HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift₂
    (by decide : 0 < 3) hSec.isWellFormed.isSNCDivisor hTrans Sec rfl hSupport hHol
  have hSecCos₁ : (geoTransformAlong M B).cosupp = (geoTransformAlong Sec B).cosupp :=
    (hLoc.wEquiv.2 B).2 hTest1
  have hSecCos₂ : (geoTransformAlong M H).cosupp = (geoTransformAlong Sec H).cosupp :=
    (hLoc.wEquiv.2 H).2 hPtest
  have hNcos₁ : (geoTransformAlong N₀ N).cosupp = {z} := by
    rw [hTransfer₁, ← hSecCos₁, joint_advanced_head_endpoint_cosupport]
    ext y
    change y.val ∈ ({q} : Set Y) ↔ y ∈ {z}
    rw [mem_singleton_iff, mem_singleton_iff, ← hq]
    exact ⟨Subtype.ext, congrArg Subtype.val⟩
  have hNcan₂ : IsCanonical N₀ (Seq.StepOneValueMasked.stepOneInvM R N₀) N₂ := by
    refine ⟨hCanN, Or.inr ?_⟩
    rw [hNcos₁, maxLocus_singleton]
  have hSec0 : Sec.cosupp = C := by
    have hh := (hLoc.wEquiv.2 T).2 trivial
    change M.cosupp = Sec.cosupp at hh
    exact hh.symm.trans joint_advanced_initial_cosupport
  have hNcos₀ : N₀.cosupp = {pN} := by
    rw [cosupp_nativePullback (Nat.le_succ 2) (zeroPlane U) (zeroPlane_regular U) Sec hSupport hHol, hSec0]
    ext y
    change y.val ∈ ({p} : Set X) ↔ y ∈ {pN}
    rw [mem_singleton_iff, mem_singleton_iff]
    constructor
    · intro he
      exact Subtype.ext he
    · intro he
      exact congrArg Subtype.val he
  have hResolve : (geoTransformAlong M H).cosupp = ∅ := resolve_stage (A := A) hC₂ ρ hρ
  have hNativeResolve : (geoTransformAlong N₀ N₂).cosupp = ∅ := by
    rw [hTransfer₂, ← hSecCos₂, hResolve, preimage_empty]
  exact ⟨V, hVc, hV, N, z, A, ρ, C₂, hρ, W, isClosed_closure, hW, N₂, hC₂, hLift,
    hLift₂, ⟨ρₙ, hρₙ, rfl⟩, hPcan, hNcan₂,
    ⟨joint_advanced_initial_cosupport, joint_advanced_head_initial_exact_comparison.2⟩,
    ⟨hNcos₀, joint_advanced_head_initial_exact_comparison.1⟩,
    ⟨joint_advanced_head_endpoint_cosupport, joint_advanced_head_exact_upper_value⟩,
    ⟨hNcos₁, hq, hValN⟩, hResolve, hNativeResolve⟩

end
end Hironaka.HironakaG1LaterAdvancedHeadTerminalExample
