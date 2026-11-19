import Hironaka.Resolution.HironakaG1RecursiveBornOrderTwoBarExample
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.Resolution.HironakaActualCoefficientDivisorExponentGap
import Hironaka.Resolution.HironakaG8HomStable
import Hironaka.Resolution.HironakaG1RecursiveBornOrderExample
import Hironaka.Resolution.HironakaG8GapNormalizedExponent

/-! A genuine born submark divisor through a surviving canonical point. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Hironaka.HironakaG1BornSubmarkPoint

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaG1LaterPositiveNormalExample
  HironakaActualCentreJointJets HironakaActualCoherentWeightedCoefficientMarked
  RelativePrincipalizationSpan GermIdealPullbackCalculus
  InvertibleIdealQuotient IdealWeightPowers BlowupControlledTransform
  HomogenizedGlueingTower BlowupFunctionTransform HironakaRelativeNormalIdeal
  GermIdealOrder CanonicalCentres ResolutionInvariantSpec RestrictedIdealExtension HironakaG8LogClosureHistory

noncomputable section

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev C : Set X := {p}

private def sourceGen (j : Fin 3) (z : X) : ℂ :=
  z.val j ^ (if j = 1 then 4 else 3)

private theorem sourceGen_mdifferentiable (j : Fin 3) : MDifferentiable 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ) (sourceGen j) := by
  have h : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ) ∞
      (fun w : X => w.val j) :=
    (EuclideanSpace.proj j : ComplexModel 3 →L[ℂ] ℂ).contMDiff.comp contMDiff_subtype_val
  exact fun z => (h.contMDiffAt (x := z)).mdifferentiableAt (by simp) |>.pow _

private theorem sourceGen_hol (j : Fin 3) (z : X) : HolomorphicAt 3 (sourceGen j) z :=
  Eventually.of_forall (sourceGen_mdifferentiable j)

open HironakaG1RecursiveBornFiniteExample (stage_carrier)
open CompanionReduction GermOrderProduct DivisorExponentAlong
open HironakaActualCoherentWeightedCoefficientMarked
/-- The whole coherent coordinate powers at the actual mark two. -/
def record : MarkedIdeal 3 X := ⟨univ, [], finiteFunctionIdeal sourceGen, 2⟩

private theorem record_coherent : record.ideal.IsCoherent :=
  isCoherent_finiteFunctionIdeal sourceGen sourceGen_mdifferentiable


private theorem sourceGen_mem (j : Fin 3) (z : X) :
    record.ideal.mem z (sourceGen j) :=
  isInSpanAt_self ⟨j, rfl⟩ (sourceGen_hol j z)

private theorem p_val : p.val = 0 := map_zero (tangentInclusion 2 1)

/-- The generators in the controlled chart are the squared first and third ratios and the linear middle coordinate. -/
private def quotientGen (j : Fin 3) (z : Y) : ℂ :=
  exceptionalCoordinate z * (if j = 1 then yChart.toFun z j else yChart.toFun z j ^ 3)

private theorem quotientGen_hol (j : Fin 3) {z : Y} (hz : z ∈ yChart.source) :
    HolomorphicAt 3 (quotientGen j) z := by
  have hLin := yChart.holomorphicAt_coord hz 1
  have he : exceptionalCoordinate =ᶠ[𝓝 z] fun w => yChart.toFun w (1 : Fin 3) := by
    filter_upwards [yChart.isOpen_source.mem_nhds hz] with w hw
    exact exceptionalCoordinate_coord w hw
  have hEx : HolomorphicAt 3 exceptionalCoordinate z := by
    filter_upwards [he.eventually_nhds, hLin] with w hEq hw
    exact hw.congr_of_eventuallyEq (Filter.EventuallyEq.symm hEq)
  unfold quotientGen
  split
  · exact hEx.mul (yChart.holomorphicAt_coord hz j)
  · exact hEx.mul (holomorphicAt_pow_of (yChart.holomorphicAt_coord hz j) 3)

private theorem generator_divides (j : Fin 3) {z : Y} (hz : z ∈ yChart.source) :
    (sourceGen j ∘ π) =ᶠ[𝓝 z] fun w => exceptionalCoordinate w ^ 2 * quotientGen j w := by
  filter_upwards [yChart.isOpen_source.mem_nhds hz] with w hw
  change (π w).val j ^ (if j = 1 then 4 else 3) = _
  rw [chart_projection w hw, monomial_apply]
  unfold quotientGen
  rw [exceptionalCoordinate_coord w hw]
  by_cases hj : j = 1
  · subst j
    simp
    ring
  · simp [hj]
    ring

/-- Each of the explicit chart generators is in the actual controlled transform. -/
private theorem quotientGen_mem (j : Fin 3) {z : Y} (hz : z ∈ yChart.source) :
    (controlledTransform hπ record.ideal 2).mem z (quotientGen j) := by
  refine mem_controlledTransform_of_eq_pow_mul
    HironakaG1LaterPositiveSelectedExample.equation_on_chart hz
    (sourceGen_mem j (π z)) (quotientGen_hol j hz) ?_
  exact generator_divides j hz

/-- Every controlled germ on the middle chart is in the span of the three
displayed generators. -/
private theorem controlled_span {z : Y} (hz : z ∈ yChart.source) {g : Y → ℂ}
    (hg : (controlledTransform hπ record.ideal 2).mem z g) :
    IsInSpanAt (n := 3) (fun b => ∃ j, b = quotientGen j) z g := by
  have hEq := HironakaG1LaterPositiveSelectedExample.equation_on_chart
  have hLambda2 := hEq.pow_mem 2 hz
  have hPB := (mem_colon_iff.mp hg).2 _ hLambda2
  have hSpan : IsInSpanAt (n := 3) (fun b => ∃ j, b = sourceGen j ∘ π) z
      (fun w => exceptionalCoordinate w ^ 2 * g w) := by
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hPB)
    rintro _ ⟨u, hu, rfl⟩
    refine (isInSpanAt_comp' hπ.contMDiff hu).mono ?_
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩
  obtain ⟨_, k, s, b, hs, hb, he⟩ := hSpan
  choose j hj using hs
  let G : Y → ℂ := fun w => ∑ l, b l w * quotientGen (j l) w
  have hG : HolomorphicAt 3 G z := HolomorphicAt.sum _ fun l _ =>
    (hb l).mul (quotientGen_hol (j l) hz)
  have hCancel : ∀ᶠ w in 𝓝 z, exceptionalCoordinate w ^ 2 * g w = exceptionalCoordinate w ^ 2 * G w := by
    filter_upwards [he, eventually_all.mpr (fun l => generator_divides (j l) hz)] with w hw hwDiv
    change exceptionalCoordinate w ^ 2 * g w = ∑ l, b l w * s l w at hw
    rw [hw, show G w = ∑ l, b l w * quotientGen (j l) w from rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hj l, hwDiv l]
    ring
  exact ⟨(mem_colon_iff.mp hg).1, k, (fun l => quotientGen (j l)), b,
    (fun l => ⟨j l, rfl⟩), hb,
    BlowupFunctionTransform.eventuallyEq_of_pow_mul hEq hz (μ := 2)
      (mem_colon_iff.mp hg).1 hG hCancel⟩

open IdealOrderArithmetic OrderTaylor CompanionReduction HomogenizedEquivalence
  HironakaG8GapNormalizedExponent BlowupStrictSubmanifold InvDomainTowerAlong
  MonomialPartEtale HironakaOneDimensionalCanonicalSuperlevels

private def chart : ComplexChart 3 Y :=
  ⟨yChart.homeo, atlasHomeo_mem_atlas yChart.toPartialEquiv (Or.inl ⟨yChart, rfl⟩)⟩
private abbrev coord (j : Fin 3) (z : Y) : ℂ := yChart.toFun z j

private theorem point_not_two {z : Y} (hz : z ∈ yChart.source) (he : coord 1 z = 0) :
    ¬ (idealPow (pointIdeal 3 z) 2).mem z (coord 1) := by
  let θ : ComplexModel 3 → Y := fun w => yChart.invFun (yChart.toFun z + w)
  have hAt : θ 0 = z := by
    change yChart.invFun (yChart.toFun z + 0) = z
    rw [add_zero]
    exact yChart.toPartialEquiv.left_inv hz
  have hDiff : ∀ᶠ w : ComplexModel 3 in 𝓝 0,
      MDifferentiableAt 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) θ w :=
    Eventually.of_forall fun w =>
      (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel 3)) chart.property
        (chart_all (yChart.toFun z + w))).comp w
          (mdifferentiableAt_const.add mdifferentiableAt_id)
  intro h
  have hVan : VanishesToOrderOn 3 (univ : Set Y) (θ 0) 2 (coord 1) :=
    ⟨coord 1, hAt.symm ▸ h, Eventually.of_forall fun _ _ => rfl⟩
  obtain ⟨b, hb, hEq⟩ := vanishesToOrderOn_comp (θ := θ) (p := (0 : ComplexModel 3)) hDiff hVan
  have hSame : (fun w : ComplexModel 3 => w (1 : Fin 3)) =ᶠ[𝓝 0] b := by
    filter_upwards [hEq] with w hw
    have hi : coord 1 (θ w) = w (1 : Fin 3) := by
      change yChart.toFun (yChart.invFun (yChart.toFun z + w)) (1 : Fin 3) = _
      have hRight : yChart.toFun (yChart.invFun (yChart.toFun z + w)) = yChart.toFun z + w :=
        yChart.toPartialEquiv.right_inv (chart_all _)
      rw [hRight]
      change coord 1 z + w (1 : Fin 3) = _
      rw [he, zero_add]
    exact hi.symm.trans (hw (mem_univ _))
  let Φ : LocalHolomorphicEquivAt (n := 3) (chartAt (ComplexModel 3) (0 : ComplexModel 3) 0) :=
    BlowupExistenceOriginIdeal.idEquivAt
  exact MonomialCase.flatCoord_notMem_idealPow_two Φ 1 (mem_flatDomain_self Φ)
    (mem_idealPow_congr hb hSame.symm)

open HironakaPrincipalizationBoundary GermIdealTotalTransform
  HironakaAdmissibleSequence HironakaOneDimensionalCanonicalSuperlevels

private theorem dom : IsInvDomain 3 record := by
  have hA := isInvDomain_univ_of_isSNCDivisor record_coherent
    (fun z => isNonzeroAlongAt_univ_iff_exists.mpr (by
      refine ⟨sourceGen 0, sourceGen_mem 0 z, ?_⟩
      intro hzero
      have hi := (productOpen U).isOpen.isOpenEmbedding_subtypeVal
      have hImage := hi.isOpenMap.image_mem_nhds hzero
      obtain ⟨_, ⟨w, hw, rfl⟩, hn⟩ := exists_coord_ne_zero_of_mem_nhds hImage (0 : Fin 3)
      have hwz : sourceGen 0 w = 0 := not_ne_iff.mp hw
      exact hn (eq_zero_of_pow_eq_zero hwz))) isSNCDivisor_nil
  exact ⟨⟨hA.isWellFormed.isClosedSubmanifold_N,hA.isWellFormed.isCoherent,
    hA.isWellFormed.isSNCDivisor,hA.isWellFormed.isTransverse⟩,
    hA.dimLE, by decide, hA.isNonzeroAlongAt⟩

private theorem initial_one : cosupport 3 record.N record.ideal 1 = ({p} : Set X) := by
  ext z
  constructor
  · intro hz
    have hf (j : Fin 3) : sourceGen j z = 0 :=
      (vanishesToOrderOn_one_iff hz.1 (sourceGen_hol j z)).mp (hz.2 _ (sourceGen_mem j z))
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    rw [p_val]
    ext j
    exact eq_zero_of_pow_eq_zero (hf j)
  · rintro rfl
    refine ⟨mem_univ _, fun g hg => ?_⟩
    refine (vanishesToOrderOn_one_iff (mem_univ _) (GermIdeal.IsCoherent.holomorphicAt_mem record_coherent hg)).mpr ?_
    obtain ⟨_, k, s, b, hs, _, he⟩ := hg
    rw [he.self_of_nhds]
    refine Finset.sum_eq_zero fun i hi => ?_
    obtain ⟨j, hj⟩ := hs i
    rw [← hj]
    simp [sourceGen, p_val]

private theorem initial_order_three : p ∈ cosupport 3 record.N record.ideal 3 := by
  have hx : p ∈ record.N := mem_univ _
  refine ⟨hx,fun g hg => ?_⟩
  apply IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn hg
  rintro _ ⟨j,rfl⟩
  have hC : HolomorphicAt 3 (fun w : X => w.val j) p := by
    have h : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ) ∞ (fun w : X => w.val j) :=
      (EuclideanSpace.proj j : ComplexModel 3 →L[ℂ] ℂ).contMDiff.comp contMDiff_subtype_val
    exact Eventually.of_forall fun w => (h.contMDiffAt (x := w)).mdifferentiableAt (by simp)
  have hv : VanishesToOrderOn 3 record.N p 1 (fun w : X => w.val j) :=
    (vanishesToOrderOn_one_iff hx hC).mpr (by rw [p_val]; rfl)
  have hv3 : VanishesToOrderOn 3 record.N p 3 (fun w : X => w.val j ^ 3) := by
    simpa only [pow_succ,pow_zero,one_mul] using (hv.mul hv).mul hv
  have hv4 : VanishesToOrderOn 3 record.N p 4 (fun w : X => w.val j ^ 4) := by
    simpa only [pow_succ] using hv3.mul hv
  change VanishesToOrderOn 3 record.N p 3 (sourceGen j)
  unfold sourceGen
  split
  · exact hv4.mono (by decide)
  · exact hv3

private theorem initial_gap : HasCosupportGap record := by
  intro x _ hx
  have he : x = p := mem_singleton_iff.mp (initial_one ▸ hx)
  exact he.symm ▸ cosupport_anti (by decide : 2 ≤ 3) initial_order_three

private theorem initial_cosupp : record.cosupp = {p} := by
  rw [← initial_one]
  exact subset_antisymm (cosupport_anti (by decide : 1 ≤ 2))
    (fun x hx => initial_gap x hx.1 hx)

private theorem isTest : IsGeoTestTower record B :=
  ⟨trivial, (PointSupportedIdealPrincipalization.singleton_geometry_and_coherence (n := 3) p).1,
    initial_cosupp.ge, hasNormalCrossings_singleton p isSNCDivisor_nil⟩

private theorem canonical {Λ : Type} [LinearOrder Λ]
    (I : ∀ {Z : CMfd.{0} 3}, BlowupTower X Z → Z → Λ) :
    IsCanonical record I B := by
  refine ⟨trivial, Or.inr ?_⟩
  change {p} = ResolutionDriver.maxLocus (I (.refl : BlowupTower X X)) record.cosupp
  rw [initial_cosupp]
  ext z
  exact ⟨fun hz => ⟨hz, fun w hw => by rw [mem_singleton_iff.mp hz, mem_singleton_iff.mp hw]⟩,
    fun hz => hz.1⟩

private abbrev A := geoTransformAlong record B
private abbrev F : Set Y := π ⁻¹' ({p} : Set X)
private theorem hN : A.N = univ := stage_carrier
private theorem hI : A.ideal = controlledTransform hπ record.ideal 2 :=
  geoTransform_ideal_eq_controlledTransform (𝔪 := record) rfl record_coherent hπ

private theorem quotient_member (j : Fin 3) {z : Y} (hz : z ∈ yChart.source) :
    A.ideal.mem z (quotientGen j) := hI.symm ▸ quotientGen_mem j hz

private theorem born_iff {z : Y} (hz : z ∈ yChart.source) :
    z ∈ F ↔ coord 1 z = 0 := by
  constructor
  · intro h
    have hi := congrArg (fun x : X => x.val (1 : Fin 3)) (mem_singleton_iff.mp h)
    change (π z).val (1 : Fin 3) = p.val (1 : Fin 3) at hi
    rw [chart_projection z hz,p_val,monomial_apply] at hi
    simpa using hi
  · intro he
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    rw [chart_projection z hz,p_val]
    ext i
    by_cases hi : i = 1
    · subst i; simpa [monomial_apply] using he
    · simp [monomial_apply,hi,he]

private theorem exceptional_eq {z : Y} (hz : z ∈ yChart.source) :
    exceptionalCoordinate =ᶠ[𝓝 z] coord 1 := by
  filter_upwards [yChart.isOpen_source.mem_nhds hz] with w hw
  exact exceptionalCoordinate_coord w hw

private theorem vanishes_congr {x : Y} {f g : Y → ℂ} {k : ℕ}
    (h : f =ᶠ[𝓝 x] g) (hf : VanishesToOrderOn 3 A.N x k f) :
    VanishesToOrderOn 3 A.N x k g := by
  obtain ⟨b,hb,he⟩ := hf
  refine ⟨b,hb,?_⟩
  filter_upwards [he,h] with w hw hfg hwN
  exact hfg.symm.trans (hw hwN)

private theorem qsurvives : q ∈ A.cosupp := by
  have hqN : q ∈ A.N := hN.symm ▸ mem_univ q
  refine ⟨hqN,fun g hg =>
    IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn (controlled_span chart_q.1 (hI ▸ hg)) ?_⟩
  rintro _ ⟨j,rfl⟩
  change VanishesToOrderOn 3 A.N q 2 (quotientGen j)
  have h1 (i : Fin 3) : VanishesToOrderOn 3 A.N q 1 (coord i) :=
    (vanishesToOrderOn_one_iff hqN (yChart.holomorphicAt_coord chart_q.1 i)).mpr
      (by change yChart.toFun q i = 0; rw [chart_q.2]; rfl)
  have hpow : VanishesToOrderOn 3 A.N q 3 (fun w => coord j w ^ 3) := by
    simpa only [pow_succ,pow_zero,one_mul] using ((h1 j).mul (h1 j)).mul (h1 j)
  have he : (fun w => coord 1 w * (if j = 1 then coord j w else coord j w ^ 3)) =ᶠ[𝓝 q]
      quotientGen j := by
    filter_upwards [exceptional_eq chart_q.1] with w hw
    unfold quotientGen
    rw [hw]
  apply vanishes_congr he
  by_cases hj : j = 1
  · simpa only [hj,if_true] using (h1 1).mul (h1 j)
  · simpa only [hj,if_false] using (h1 1).mul (hpow.mono (by decide : 1 ≤ 3))

private theorem not_two_at_simple_point {z : Y} (hz : z ∈ yChart.source)
    (he : coord 1 z = 0) (ha : coord 0 z ≠ 0) :
    z ∉ cosupport 3 A.N A.ideal 2 := by
  intro h
  have hv : VanishesToOrderOn 3 A.N z 2 (fun w => coord 1 w * coord 0 w ^ 3) := by
    apply vanishes_congr _ (h.2 _ (quotient_member 0 hz))
    filter_upwards [exceptional_eq hz] with w hw
    unfold quotientGen
    rw [hw,if_neg (by decide : (0 : Fin 3) ≠ 1)]
  have hu : ¬ (idealPow (pointIdeal 3 z) 1).mem z (fun w => coord 0 w ^ 3) :=
    fun h => pow_ne_zero 3 ha (apply_eq_zero_of_mem_idealPow_pointIdeal (x := z) le_rfl h)
  exact mul_notMem_idealPow (a := 1) (b := 0) (yChart.holomorphicAt_coord hz 1)
    (holomorphicAt_pow_of (yChart.holomorphicAt_coord hz 0) 3)
    (point_not_two hz he) hu (mem_idealPow_of_vanishesToOrderOn_univ (hN ▸ hv))

private theorem frequently_simple_born :
    ∃ᶠ z in 𝓝 q, z ∈ yChart.source ∧ coord 1 z = 0 ∧ coord 0 z ≠ 0 := by
  let w (a : ℂ) : ComplexModel 3 := a • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)
  have hW : Tendsto w (𝓝 0) (𝓝 (0 : ComplexModel 3)) := by
    have hc : Continuous w := continuous_id.smul continuous_const
    simpa [w] using hc.tendsto (0 : ℂ)
  have hi := yChart.homeo.tendsto_symm (x := q) chart_q.1
  change Tendsto yChart.invFun (𝓝 (yChart.toFun q)) (𝓝 q) at hi
  rw [chart_q.2] at hi
  have hn : ∃ᶠ a : ℂ in 𝓝 0, a ≠ 0 := by
    have ht : ∃ᶠ a : ℂ in 𝓝[≠] 0, True := (Eventually.of_forall fun _ => trivial).frequently
    exact ((frequently_nhdsWithin_iff).mp ht).mono fun _ ha => ha.2
  exact (hi.comp hW).frequently (hn.mono fun a ha => by
    have hs := yChart.toPartialEquiv.map_target (chart_all (w a))
    have hr : yChart.toFun (yChart.invFun (w a)) = w a :=
      yChart.toPartialEquiv.right_inv (chart_all (w a))
    refine ⟨hs, ?_, ?_⟩
    · change yChart.toFun (yChart.invFun (w a)) (1 : Fin 3) = 0
      rw [hr]
      simp [w]
    · change yChart.toFun (yChart.invFun (w a)) (0 : Fin 3) ≠ 0
      rw [hr]
      simpa [w] using ha)

/-- The born exponent at the actual still-surviving canonical point is one,
strictly below the genuine mark two. The full source gap held. -/
theorem actual_born_submark_at_surviving_point :
    IsInvDomain 3 record ∧ HasCosupportGap record ∧ IsGeoTestTower record B ∧
    IsCanonical record ((invFamily (by decide : 0 < 3) 3).inv record) B ∧
    q ∈ A.cosupp ∧ A.E = [F] ∧ divExpAlong 3 A.N A.ideal F q = 1 := by
  refine ⟨dom,initial_gap,isTest,canonical _,qsurvives,rfl,?_⟩
  let hA := isInvDomain_geoTransformAlong dom B isTest
  have hq0 : coord 1 q = 0 := by change yChart.toFun q 1 = 0; rw [chart_q.2]; rfl
  have hqF : q ∈ F := (born_iff chart_q.1).mpr hq0
  obtain ⟨j,hj⟩ := hA.isWellFormed.isClosedSubmanifold_N.2 q qsurvives.1
  obtain ⟨r,hr⟩ := exists_isLocalRetraction hj
  have he (e : ℕ) : IsDivNearAlong 3 A.N A.ideal F e q ↔ e ≤ divExpAlong 3 A.N A.ideal F q :=
    isDivNearAlong_iff_le_divExpAlong hr hqF (hA.isNonzeroAlongAt q qsurvives.1)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hA.isWellFormed.isCoherent hg)
  have h1 : 1 ≤ divExpAlong 3 A.N A.ideal F q := (he 1).mp (by
    filter_upwards [yChart.isOpen_source.mem_nhds chart_q.1] with z hz hzN hzF
    refine ⟨hzN,fun g hg => ?_⟩
    apply IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn (controlled_span hz (hI ▸ hg))
    rintro _ ⟨j,rfl⟩
    apply (vanishesToOrderOn_one_iff hzN (quotientGen_hol j hz)).mpr
    have hZero := (exceptionalCoordinate_coord z hz).trans ((born_iff hz).mp hzF)
    unfold quotientGen
    rw [hZero,zero_mul])
  have h2 : ¬ 2 ≤ divExpAlong 3 A.N A.ideal F q := by
    intro h
    obtain ⟨z,⟨hz,hy,hx⟩,hd⟩ := (frequently_simple_born.and_eventually ((he 2).mpr h)).exists
    exact not_two_at_simple_point hz hy hx (hd (hN.symm ▸ mem_univ z) ((born_iff hz).mpr hy))
  omega

open HomogenizedIdealAlong HironakaG8HomStable HironakaActualCoefficientDivisorExponentGap
  HironakaActualInitialNonmonomialCoefficientBoundary

/-- Refreshing the whole coefficient ideal at the actual controlled
stage removes the born submark exponent, although the canonical point
remains in the same marked cosupport. -/
theorem actual_coefficient_refresh_removes_born_submark :
    let D := coeffMarkedAlong A
    IsInvDomain 3 D ∧ D.N = A.N ∧ D.E = A.E ∧ D.cosupp = A.cosupp ∧
      q ∈ D.cosupp ∧ divExpAlong 3 D.N D.ideal F q = 0 := by
  intro D
  let hA := isInvDomain_geoTransformAlong dom B isTest
  have hD : IsInvDomain 3 D := coefficient_isInvDomain A hA
  have hCos : D.cosupp = A.cosupp := cosupp_coeffMarkedAlong
    hA.isWellFormed.isClosedSubmanifold_N.2
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hA.isWellFormed.isCoherent hg) hA.one_le_d
  have hGap : HasCosupportGap D := by
    intro x _ hx
    change x ∈ cosupport 3 A.N (coeffMarkedAlong A).ideal (coeffMarkedAlong A).d
    rw [← coefficient_restriction_cosupport_gap A hA.isWellFormed.isClosedSubmanifold_N
      hA.isWellFormed.isCoherent hA.one_le_d A.N (fun _ h => h)]
    exact hx
  refine ⟨hD,rfl,rfl,hCos,hCos.symm ▸ qsurvives,?_⟩
  by_contra! hPos
  have hq0 : coord 1 q = 0 := by change yChart.toFun q 1 = 0; rw [chart_q.2]; rfl
  have hqF : q ∈ F := (born_iff chart_q.1).mpr hq0
  obtain ⟨j,hj⟩ := hD.isWellFormed.isClosedSubmanifold_N.2 q qsurvives.1
  obtain ⟨r,hr⟩ := exists_isLocalRetraction hj
  have he (e : ℕ) : IsDivNearAlong 3 D.N D.ideal F e q ↔ e ≤ divExpAlong 3 D.N D.ideal F q :=
    isDivNearAlong_iff_le_divExpAlong hr hqF (hD.isNonzeroAlongAt q qsurvives.1)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hD.isWellFormed.isCoherent hg)
  have hNear := (he 1).mpr (Nat.pos_of_ne_zero hPos)
  obtain ⟨z,⟨hz,hy,hx⟩,h⟩ := (frequently_simple_born.and_eventually hNear).exists
  have hzF : z ∈ F := (born_iff hz).mpr hy
  have hzN : z ∈ D.N := hN.symm ▸ mem_univ z
  have hzD := hGap z hzN (h hzN hzF)
  have hzA : z ∈ A.cosupp := hCos ▸ hzD
  exact not_two_at_simple_point hz hy hx hzA

open HironakaG1RecursiveBornOrderTwoBarExample MarkedIdealOperationsTransform
  DerivativeIdealAlong DerivativeIdealAlongCoherent GiraudAlong RestrictedIdealExtension
  MarkedIdealOperationsAlong HadamardBridge TangentDirectionAlong HironakaG8CoeffClass

private theorem le_centre_pow {I : GermIdeal 3 X} (hI : I.IsCoherent) (m : ℕ)
    (hp : p ∈ cosupport 3 univ I m) :
    I.Le (idealPow (vanishingIdeal (n := 3) ({p} : Set X)) m) := by
  intro x g hg
  by_cases hx : x = p
  · subst x
    exact mem_idealPow_of_vanishesToOrderOn_univ (hp.2 _ hg)
  · apply mem_idealPow_of_one_mem (I := vanishingIdeal (n := 3) ({p} : Set X)) _
      (GermIdeal.IsCoherent.holomorphicAt_mem hI hg)
    refine ⟨holomorphicAt_const 1, ?_⟩
    have hx' : x ∉ ({p} : Set X) := hx
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx'] with z hZ hz
    exact (hZ hz).elim

private abbrev rawDerivative := derivIdealAlong record.N record.ideal
private abbrev derivativeStage := controlledTransform hπ rawDerivative 1
private abbrev sourceCoefficient := coeffMarkedAlong record
private abbrev inheritedCoefficient := geoTransformAlong sourceCoefficient B

private theorem derivative_coherent : rawDerivative.IsCoherent :=
  isCoherent_derivIdealAlong dom.isWellFormed.isCoherent dom.isWellFormed.isClosedSubmanifold_N

private theorem derivative_order_two : p ∈ cosupport 3 univ rawDerivative 2 := by
  have h := cosupport_add_subset_cosupport_iterDerivIdealAlong
    (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem record_coherent h)
    2 1 initial_order_three
  exact h

private theorem derivative_le_centre : rawDerivative.Le
    (idealPow (vanishingIdeal (n := 3) ({p} : Set X)) 2) :=
  le_centre_pow derivative_coherent 2 derivative_order_two

private theorem derivative_le_centre_one : rawDerivative.Le
    (idealPow (vanishingIdeal (n := 3) ({p} : Set X)) 1) :=
  le_centre_pow derivative_coherent 1 (cosupport_anti (by decide : 1 ≤ 2) derivative_order_two)

private theorem derivative_stage_pos {z : Y} (hz : z ∈ yChart.source)
    (hF : z ∈ F) : z ∈ cosupport 3 univ derivativeStage 1 := by
  let hEq := HironakaG1LaterPositiveSelectedExample.equation_on_chart
  refine ⟨mem_univ z,fun g hg => ?_⟩
  apply IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn
    ((mem_controlledTransform_iff hEq hz derivative_coherent derivative_le_centre_one g).mp hg)
  rintro v ⟨hv,u,hu,hvEq⟩
  obtain ⟨w,hw,hwEq⟩ := exists_eq_pow_mul hEq hz (derivative_le_centre _ _ hu)
  have h' : (fun a => exceptionalCoordinate a ^ 1 * v a) =ᶠ[𝓝 z]
      (fun a => exceptionalCoordinate a ^ 1 * (exceptionalCoordinate a * w a)) := by
    filter_upwards [hvEq,hwEq] with a h1 h2
    rw [← h1,h2]
    ring
  have hHz : HolomorphicAt 3 exceptionalCoordinate z := hEq.holomorphicAt hz
  have hSame := eventuallyEq_of_pow_mul hEq hz (μ := 1) hv (hHz.mul hw) h'
  have hEx0 := (exceptionalCoordinate_coord z hz).trans ((born_iff hz).mp hF)
  apply (vanishesToOrderOn_one_iff (mem_univ z) hv).mpr
  rw [hSame.self_of_nhds]
  change exceptionalCoordinate z * w z = 0
  rw [hEx0,zero_mul]

private theorem inherited_ideal :
    inheritedCoefficient.ideal = sumIdeal A.ideal (idealPow derivativeStage 2) := by
  obtain ⟨hMark,hCoeff⟩ := coefficient_mark_two record dom.isWellFormed rfl
  change (sourceCoefficient.geoTransform ({p} : Set X) π).ideal = _
  have hEq := geoTransform_ideal_eq_controlledTransform (𝔪 := sourceCoefficient) rfl
    (coefficient_isInvDomain record dom).isWellFormed.isCoherent hπ
  rw [hEq,hMark,hCoeff,hI]
  have hSum := controlledTransform_sumIdeal_idealPow hπ record_coherent derivative_coherent
    (le_centre_pow record_coherent 2 (cosupport_anti (by decide : 2 ≤ 3) initial_order_three))
      derivative_le_centre_one
  have hAcoh := (isInvDomain_geoTransformAlong dom B isTest).isWellFormed.isCoherent
  have hP := idealPow_one_eq (𝔞 := controlledTransform hπ record.ideal 2) (hI ▸ hAcoh)
  rw [idealPow_one_eq record_coherent,hP] at hSum
  exact hSum

private theorem inherited_cosupport_on_born {z : Y} (hz : z ∈ yChart.source)
    (hF : z ∈ F) :
    z ∈ inheritedCoefficient.cosupp ↔ z ∈ A.cosupp := by
  have hA := isInvDomain_geoTransformAlong dom B isTest
  have hDcoh := isCoherent_controlledTransform hπ derivative_coherent derivative_le_centre_one
  obtain ⟨hMark,_⟩ := coefficient_mark_two record dom.isWellFormed rfl
  have hN' : inheritedCoefficient.N = A.N := rfl
  have hd : inheritedCoefficient.d = 2 := (d_geoTransformAlong sourceCoefficient B).trans hMark
  change z ∈ cosupport 3 inheritedCoefficient.N inheritedCoefficient.ideal inheritedCoefficient.d ↔
    z ∈ A.cosupp
  rw [hN',hd,inherited_ideal,cosupport_sumIdeal
    (fun _ _ g => GermIdeal.IsCoherent.holomorphicAt_mem hA.isWellFormed.isCoherent g)
    (fun _ _ g => GermIdealOrder.holomorphicAt_of_mem_idealPow g)]
  have hD := cosupport_subset_cosupport_idealPow (N := (univ : Set Y)) (𝔞 := derivativeStage) 1 2
    (derivative_stage_pos hz hF)
  have hDP : z ∈ cosupport 3 A.N (idealPow derivativeStage 2) 2 := hN.symm ▸ hD
  exact and_iff_left hDP

/-- Exact coefficient inheritance survives the actual canonical blowup
as an analytic record with a born submark at a surviving point. Its
ideal is the controlled source coefficient ideal, without an equality
hypothesis between refreshed and controlled germs. -/
theorem inherited_coefficient_born_submark_at_survivor :
    IsInvDomain 3 sourceCoefficient ∧ HasCosupportGap sourceCoefficient ∧
      IsGeoTestTower sourceCoefficient B ∧ q ∈ inheritedCoefficient.cosupp ∧
      divExpAlong 3 inheritedCoefficient.N inheritedCoefficient.ideal F q = 1 := by
  have hC := coefficient_isInvDomain record dom
  have hGap : HasCosupportGap sourceCoefficient := by
    intro x _ hx
    change x ∈ cosupport 3 record.N sourceCoefficient.ideal sourceCoefficient.d
    exact (coefficient_restriction_cosupport_gap record dom.isWellFormed.isClosedSubmanifold_N
      record_coherent dom.one_le_d record.N (fun _ h => h)) ▸ hx
  have hCos : sourceCoefficient.cosupp = record.cosupp := cosupp_coeffMarkedAlong
    dom.isWellFormed.isClosedSubmanifold_N.2
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem record_coherent hg) dom.one_le_d
  have hTest : IsGeoTestTower sourceCoefficient B :=
    ⟨trivial, (PointSupportedIdealPrincipalization.singleton_geometry_and_coherence (n := 3) p).1,
      (hCos.trans initial_cosupp).ge,hasNormalCrossings_singleton p isSNCDivisor_nil⟩
  have hA' := isInvDomain_geoTransformAlong hC B hTest
  have hq0 : coord 1 q = 0 := by change yChart.toFun q 1 = 0; rw [chart_q.2]; rfl
  have hqF : q ∈ F := (born_iff chart_q.1).mpr hq0
  have hq := (inherited_cosupport_on_born chart_q.1 hqF).mpr qsurvives
  refine ⟨hC,hGap,hTest,hq,?_⟩
  obtain ⟨k,hk⟩ := hA'.isWellFormed.isClosedSubmanifold_N.2 q hq.1
  obtain ⟨r,hr⟩ := exists_isLocalRetraction hk
  have he (e : ℕ) : IsDivNearAlong 3 inheritedCoefficient.N inheritedCoefficient.ideal F e q ↔
      e ≤ divExpAlong 3 inheritedCoefficient.N inheritedCoefficient.ideal F q :=
    isDivNearAlong_iff_le_divExpAlong hr hqF (hA'.isNonzeroAlongAt q hq.1)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hA'.isWellFormed.isCoherent hg)
  have hA := isInvDomain_geoTransformAlong dom B isTest
  have h1 : 1 ≤ divExpAlong 3 inheritedCoefficient.N inheritedCoefficient.ideal F q := (he 1).mp (by
    filter_upwards [yChart.isOpen_source.mem_nhds chart_q.1] with z hz _ hzF
    have hzA : z ∈ cosupport 3 A.N A.ideal 1 := by
      have hqN : z ∈ A.N := hN.symm ▸ mem_univ z
      refine ⟨hqN,fun g hg => ?_⟩
      apply IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn (controlled_span hz (hI ▸ hg))
      rintro _ ⟨j,rfl⟩
      apply (vanishesToOrderOn_one_iff hqN (quotientGen_hol j hz)).mpr
      have hZero := (exceptionalCoordinate_coord z hz).trans ((born_iff hz).mp hzF)
      unfold quotientGen
      rw [hZero,zero_mul]
    have hDP := cosupport_subset_cosupport_idealPow (N := (univ : Set Y))
      (𝔞 := derivativeStage) 1 2 (derivative_stage_pos hz hzF)
    have hDP' : z ∈ cosupport 3 A.N (idealPow derivativeStage 2) 1 :=
      cosupport_anti (by decide : 1 ≤ 2) (hN.symm ▸ hDP)
    change z ∈ cosupport 3 A.N inheritedCoefficient.ideal 1
    rw [inherited_ideal,cosupport_sumIdeal
      (fun _ _ g => GermIdeal.IsCoherent.holomorphicAt_mem hA.isWellFormed.isCoherent g)
      (fun _ _ g => GermIdealOrder.holomorphicAt_of_mem_idealPow g)]
    exact ⟨hzA,hDP'⟩)
  have h2 : ¬ 2 ≤ divExpAlong 3 inheritedCoefficient.N inheritedCoefficient.ideal F q := by
    intro h
    obtain ⟨z,⟨hz,hy,hx⟩,hd⟩ := (frequently_simple_born.and_eventually ((he 2).mpr h)).exists
    have hzF := (born_iff hz).mpr hy
    have hzN : z ∈ inheritedCoefficient.N := hN.symm ▸ mem_univ z
    have hm : inheritedCoefficient.d = 2 := (d_geoTransformAlong sourceCoefficient B).trans
      (coefficient_mark_two record dom.isWellFormed rfl).1
    have hcos : z ∈ inheritedCoefficient.cosupp := by
      change z ∈ cosupport 3 inheritedCoefficient.N inheritedCoefficient.ideal inheritedCoefficient.d
      rw [hm]
      exact hd hzN hzF
    exact not_two_at_simple_point hz hy hx ((inherited_cosupport_on_born hz hzF).mp hcos)
  omega

/-- On the exact inherited coefficient record, all source gap and
coherence conditions hold. At the same surviving canonical point,
its actual controlled born exponent is one while refreshing the
coefficient ideal gives exponent zero on the identical ordered slot. -/
theorem exact_inherited_coefficient_born_refresh_mismatch :
    let P := coeffMarkedAlong record
    let Q := geoTransformAlong P B
    let D := coeffMarkedAlong Q
    P.d = 2 ∧ P.E = [] ∧ IsInvDomain 3 P ∧ HasCosupportGap P ∧
      IsGeoTestTower P B ∧ IsCanonical P ((invFamily (by decide : 0 < 3) 3).inv P) B ∧
      Q.d = 2 ∧ Q.E = [F] ∧ D.E = Q.E ∧ D.N = Q.N ∧
      q ∈ Q.cosupp ∧ q ∈ D.cosupp ∧
      divExpAlong 3 Q.N Q.ideal F q = 1 ∧ divExpAlong 3 D.N D.ideal F q = 0 := by
  intro P Q D
  obtain ⟨hP,hGap,hTest,hq,hExp⟩ := inherited_coefficient_born_submark_at_survivor
  have hMark : P.d = 2 := (coefficient_mark_two record dom.isWellFormed rfl).1
  have hQd : Q.d = 2 := (d_geoTransformAlong P B).trans hMark
  have hCosP : P.cosupp = record.cosupp := cosupp_coeffMarkedAlong
    dom.isWellFormed.isClosedSubmanifold_N.2
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem record_coherent hg) dom.one_le_d
  have hCan : IsCanonical P ((invFamily (by decide : 0 < 3) 3).inv P) B := by
    refine ⟨trivial,Or.inr ?_⟩
    change {p} = ResolutionDriver.maxLocus
      ((invFamily (by decide : 0 < 3) 3).inv P (.refl : BlowupTower X X)) P.cosupp
    rw [hCosP,initial_cosupp]
    ext z
    exact ⟨fun hz => ⟨hz,fun w hw => by rw [mem_singleton_iff.mp hz,mem_singleton_iff.mp hw]⟩,
      fun hz => hz.1⟩
  have hQ := isInvDomain_geoTransformAlong hP B hTest
  have hD := coefficient_isInvDomain Q hQ
  have hCos : D.cosupp = Q.cosupp := cosupp_coeffMarkedAlong
    hQ.isWellFormed.isClosedSubmanifold_N.2
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hg) hQ.one_le_d
  have hGapD : HasCosupportGap D := by
    intro x _ hx
    change x ∈ cosupport 3 Q.N (coeffMarkedAlong Q).ideal (coeffMarkedAlong Q).d
    rw [← coefficient_restriction_cosupport_gap Q hQ.isWellFormed.isClosedSubmanifold_N
      hQ.isWellFormed.isCoherent hQ.one_le_d Q.N (fun _ h => h)]
    exact hx
  refine ⟨hMark,rfl,hP,hGap,hTest,hCan,hQd,rfl,rfl,rfl,hq,hCos.symm ▸ hq,hExp,?_⟩
  by_contra! hPos
  have hq0 : coord 1 q = 0 := by change yChart.toFun q 1 = 0; rw [chart_q.2]; rfl
  have hqF := (born_iff chart_q.1).mpr hq0
  obtain ⟨j,hj⟩ := hD.isWellFormed.isClosedSubmanifold_N.2 q hq.1
  obtain ⟨r,hr⟩ := exists_isLocalRetraction hj
  have he (e : ℕ) : IsDivNearAlong 3 D.N D.ideal F e q ↔ e ≤ divExpAlong 3 D.N D.ideal F q :=
    isDivNearAlong_iff_le_divExpAlong hr hqF (hD.isNonzeroAlongAt q hq.1)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hD.isWellFormed.isCoherent hg)
  obtain ⟨z,⟨hz,hy,hx⟩,h⟩ :=
    (frequently_simple_born.and_eventually ((he 1).mpr (Nat.pos_of_ne_zero hPos))).exists
  have hzF := (born_iff hz).mpr hy
  have hzN : z ∈ D.N := hN.symm ▸ mem_univ z
  have hzD := hGapD z hzN (h hzN hzF)
  have hzQ : z ∈ Q.cosupp := hCos ▸ hzD
  exact not_two_at_simple_point hz hy hx ((inherited_cosupport_on_born hz hzF).mp hzQ)

#print axioms actual_born_submark_at_surviving_point
#print axioms actual_coefficient_refresh_removes_born_submark
#print axioms inherited_coefficient_born_submark_at_survivor
#print axioms exact_inherited_coefficient_born_refresh_mismatch

end
end Hironaka.HironakaG1BornSubmarkPoint
