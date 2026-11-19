import Hironaka.Resolution.HironakaG1LaterPositiveSuccessorRead
import Hironaka.Resolution.HironakaG1RecursiveBornFiniteExample
import Hironaka.Resolution.HironakaActualCoefficientNonmonomialHistoryOrder

/-! Order calculations for the actual middle chart of the canonical point blowup. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1RecursiveBornOrderExample
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  GermIdealOrder IdealOrderArithmetic OrderTaylor CompanionReduction IdealWeightPowers MonomialPartEtale BlowupControlledTransform
  InvertibleIdealQuotient RelativePrincipalizationSpan InvDomainTowerAlong
  HironakaG1LaterPositiveNormalExample HironakaG1RecursiveBornFiniteExample
  HironakaSharpOriginalProductTraceOrder NonmonomialOrderLocal

private abbrev A := geoTransformAlong record B
private def chart : ComplexChart 3 Y :=
  ⟨yChart.homeo, atlasHomeo_mem_atlas yChart.toPartialEquiv (Or.inl ⟨yChart, rfl⟩)⟩
private abbrev coord (j : Fin 3) (z : Y) : ℂ := yChart.toFun z j

private theorem coord_vanish (j : Fin 3) :
    VanishesToOrderOn 3 A.N q 1 (coord j) :=
  (vanishesToOrderOn_one_iff survivor.1 (yChart.holomorphicAt_coord chart_q.1 j)).mpr
    (by change yChart.toFun q j = 0; rw [chart_q.2]; rfl)

private theorem exceptional_eq {z : Y} (hz : z ∈ yChart.source) :
    exceptionalCoordinate =ᶠ[𝓝 z] coord 1 := by
  filter_upwards [yChart.isOpen_source.mem_nhds hz] with w hw
  exact exceptionalCoordinate_coord w hw

private theorem vanishes_congr {x : Y} {f g : Y → ℂ} {k : ℕ}
    (h : f =ᶠ[𝓝 x] g) (hf : VanishesToOrderOn 3 A.N x k f) :
    VanishesToOrderOn 3 A.N x k g := by
  obtain ⟨b, hb, he⟩ := hf
  refine ⟨b, hb, ?_⟩
  filter_upwards [he, h] with w hw hfg hwN
  exact hfg.symm.trans (hw hwN)

/-- The actual transformed ideal vanishes at least twice at the middle-chart origin. -/
theorem stage_cosupport_two : q ∈ cosupport 3 A.N A.ideal 2 := by
  refine ⟨survivor.1, fun g hg => IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn ((stage_span chart_q.1 g).mp hg) ?_⟩
  rintro _ ⟨j, rfl⟩
  refine vanishes_congr ?_ (show VanishesToOrderOn 3 A.N q 2
    (fun z => coord 1 z * (if j = 1 then coord j z else coord j z ^ 2)) from ?_)
  · filter_upwards [exceptional_eq chart_q.1] with z hz
    unfold quotientGen
    rw [hz]
  · by_cases hj : j = 1
    · simpa only [hj, if_true] using (coord_vanish 1).mul (coord_vanish j)
    · simpa only [hj, if_false, pow_two] using
        (coord_vanish 1).mul (((coord_vanish j).mul (coord_vanish j)).mono (by decide : 1 ≤ 2))

open HomogenizedEquivalence

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

private theorem quotient_member (j : Fin 3) {z : Y} (hz : z ∈ yChart.source) :
    A.ideal.mem z (quotientGen j) := by
  have hI : A.ideal = controlledTransform hπ record.ideal 1 :=
    geoTransform_ideal_eq_controlledTransform (𝔪 := record) rfl domain.isWellFormed.isCoherent hπ
  rw [hI]
  exact quotientGen_mem j hz

/-- The square of the exceptional coordinate prevents order three at the origin. -/
theorem stage_not_cosupport_three : q ∉ cosupport 3 A.N A.ideal 3 := by
  intro h
  have hMem := quotient_member 1 chart_q.1
  have hv : VanishesToOrderOn 3 A.N q 3 (fun z => coord 1 z ^ 2) := by
    refine vanishes_congr ?_ (h.2 _ hMem)
    filter_upwards [exceptional_eq chart_q.1] with z hz
    simp only [quotientGen, if_true, hz, pow_two]
  have hn := point_not_two chart_q.1 (by change yChart.toFun q 1 = 0; rw [chart_q.2]; rfl)
  exact pow_notMem_idealPow (o := 1) (yChart.holomorphicAt_coord chart_q.1 1) hn 2
    (mem_idealPow_of_vanishesToOrderOn_univ (stage_carrier ▸ hv))

/-- The whole transformed ideal has ordinary order exactly two at the survivor. -/
theorem stage_ordinary_order : ordinaryTraceOrder (X := Y) A.N A.ideal q = 2 := by
  have hd := isInvDomain_geoTransformAlong domain B test
  have h2 : 2 ≤ ordinaryTraceOrder (X := Y) A.N A.ideal q := (ordinaryTraceOrder_cosupport_iff hd.isWellFormed.isClosedSubmanifold_N
    hd.isWellFormed.isCoherent hd.isNonzeroAlongAt survivor.1 2).mp stage_cosupport_two
  have h3 : ¬ 3 ≤ ordinaryTraceOrder (X := Y) A.N A.ideal q := (ordinaryTraceOrder_cosupport_iff hd.isWellFormed.isClosedSubmanifold_N
    hd.isWellFormed.isCoherent hd.isNonzeroAlongAt survivor.1 3).not.mp stage_not_cosupport_three
  omega
open DivisorExponentAlong GermOrderProduct MonomialCase MonomialCaseAlong
  HironakaActualCoefficientNonmonomialHistoryOrder HironakaRelativeNormalIdeal
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar

private abbrev F : Set Y := List.head! A.E
private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩

/-- The only boundary slot at the endpoint is the exceptional divisor. -/
theorem stage_boundary : A.E = [π ⁻¹' ({p} : Set X)] := rfl

private theorem born_iff {z : Y} (hz : z ∈ yChart.source) :
    z ∈ F ↔ coord 1 z = 0 := by
  have hF : F = π ⁻¹' ({p} : Set X) := by rw [show F = A.E.head! from rfl, stage_boundary]; rfl
  rw [hF]
  have hp : p.val = 0 := map_zero (tangentInclusion 2 1)
  constructor
  · intro h
    have hi := congrArg (fun x : X => x.val (1 : Fin 3)) (mem_singleton_iff.mp h)
    change (π z).val (1 : Fin 3) = p.val (1 : Fin 3) at hi
    rw [chart_projection z hz, hp, monomial_apply] at hi
    simpa using hi
  · intro he
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    rw [chart_projection z hz, hp]
    ext i
    by_cases hi : i = 1
    · subst i
      simpa [monomial_apply] using he
    · simp [monomial_apply, hi, he]

private theorem not_two_at_simple_point {z : Y} (hz : z ∈ yChart.source)
    (he : coord 1 z = 0) (ha : coord 0 z ≠ 0) :
    z ∉ cosupport 3 A.N A.ideal 2 := by
  intro h
  have hv : VanishesToOrderOn 3 A.N z 2 (fun w => coord 1 w * (coord 0 w * coord 0 w)) := by
    refine vanishes_congr ?_ (h.2 _ (quotient_member 0 hz))
    filter_upwards [exceptional_eq hz] with w hw
    unfold quotientGen
    rw [hw]
    simp only [show (0 : Fin 3) ≠ 1 by decide, if_false]
    rw [pow_two]
  have hu : ¬ (idealPow (pointIdeal 3 z) 1).mem z (fun w => coord 0 w * coord 0 w) :=
    fun h => mul_ne_zero ha ha (apply_eq_zero_of_mem_idealPow_pointIdeal (x := z) le_rfl h)
  exact mul_notMem_idealPow (a := 1) (b := 0) (yChart.holomorphicAt_coord hz 1)
    ((yChart.holomorphicAt_coord hz 0).mul (yChart.holomorphicAt_coord hz 0))
    (point_not_two hz he) hu (mem_idealPow_of_vanishesToOrderOn_univ (stage_carrier ▸ hv))

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

/-- The unique exceptional divisor has exponent one in the actual transformed ideal. -/
theorem stage_exceptional_exponent : divExpAlong 3 A.N A.ideal F q = 1 := by
  have hd := isInvDomain_geoTransformAlong domain B test
  have hqF : q ∈ F := (born_iff chart_q.1).mpr (by change yChart.toFun q 1 = 0; rw [chart_q.2]; rfl)
  obtain ⟨k, hk⟩ := hd.isWellFormed.isClosedSubmanifold_N.2 q survivor.1
  obtain ⟨r, hr⟩ := exists_isLocalRetraction hk
  have he (e : ℕ) : IsDivNearAlong 3 A.N A.ideal F e q ↔ e ≤ divExpAlong 3 A.N A.ideal F q :=
    isDivNearAlong_iff_le_divExpAlong hr hqF (hd.isNonzeroAlongAt q survivor.1)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hd.isWellFormed.isCoherent hg)
  have h1 : 1 ≤ divExpAlong 3 A.N A.ideal F q := (he 1).mp (by
    filter_upwards [yChart.isOpen_source.mem_nhds chart_q.1] with z hz _ hzF
    exact (stage_cosupport_iff hz).mpr
      ((exceptionalCoordinate_coord z hz).trans ((born_iff hz).mp hzF)))
  have h2 : ¬ 2 ≤ divExpAlong 3 A.N A.ideal F q := by
    intro h
    have hh := frequently_simple_born.and_eventually ((he 2).mpr h)
    obtain ⟨z, ⟨hz, he0, ha⟩, hzDiv⟩ := hh.exists
    exact not_two_at_simple_point hz he0 ha
      (hzDiv (stage_carrier.symm ▸ mem_univ z) ((born_iff hz).mpr he0))
  omega

/-- Removing the exceptional factor leaves nonmonomial order one at the survivor. -/
theorem stage_nonmonomial_order : nmOrd A q = 1 := by
  have hd := isInvDomain_geoTransformAlong domain B test
  have hqF : q ∈ F := (born_iff chart_q.1).mpr (by change yChart.toFun q 1 = 0; rw [chart_q.2]; rfl)
  have hE : A.E = [F] := by rw [show F = A.E.head! from rfl, stage_boundary]; rfl
  have hIdx : memberIdx A.E q = {0} := by
    ext i
    rw [hE, mem_memberIdx]
    simp [hqF]
  have hSum : (∑ i ∈ memberIdx A.E q, expDataAlong 3 A.N A.ideal A.E q i) = 1 := by
    rw [hIdx, Finset.sum_singleton]
    unfold expDataAlong
    simp only [hE, List.length_singleton, Nat.zero_lt_one, dite_true, List.get_eq_getElem,
      List.getElem_singleton]
    exact stage_exceptional_exponent
  have h := (whole_factor_order (by decide : 0 < 3) A hd.isWellFormed hd.isNonzeroAlongAt q survivor.1).2.2.1
  change ordinaryTraceOrder (X := Y) A.N A.ideal q =
    (∑ i ∈ memberIdx A.E q, expDataAlong 3 A.N A.ideal A.E q i) + nmOrd A q at h
  rw [stage_ordinary_order, hSum] at h
  omega

open NonmonomialOrderRegime NonmonomialOrderTail GeneralValue ResolutionInvariantSpec
  StepOneValue StepOneValueMasked HironakaG1LaterPositiveSuccessorRead
  CompanionRebase CompanionReductionAlong BlowupTowerSplit StepOneRegime CanonicalCentres

private theorem source_order_ge_two (x : X) (hx : x ∈ record.cosupp) :
    2 ≤ nmOrd record x := by
  have he : x = p := mem_singleton_iff.mp (by rw [← show record.cosupp = {p} from initial_cosupport]; exact hx)
  subst x
  obtain ⟨_, _, hOrd, _⟩ := whole_factor_order (by decide : 0 < 3) record domain.isWellFormed
    domain.isNonzeroAlongAt p hx.1
  have hSame : ordinaryTraceOrder (X := X) record.N record.ideal p = nmOrd record p := by
    have hIdx : memberIdx record.E p = ∅ := by
      ext i
      simp [mem_memberIdx, record]
    change ordinaryTraceOrder (X := X) record.N record.ideal p =
      (∑ i ∈ memberIdx record.E p, expDataAlong 3 record.N record.ideal record.E p i) + nmOrd record p at hOrd
    simpa only [hIdx, Finset.sum_empty, zero_add] using hOrd
  rw [← hSame]
  apply (ordinaryTraceOrder_cosupport_iff domain.isWellFormed.isClosedSubmanifold_N
    domain.isWellFormed.isCoherent domain.isNonzeroAlongAt hx.1 2).mp
  refine ⟨hx.1, fun g hg => ?_⟩
  unfold record at hg
  refine IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn hg ?_
  rintro _ ⟨j, rfl⟩
  change VanishesToOrderOn 3 record.N p 2
    (fun x : X => x.val j ^ (if j = 1 then 3 else 2))
  have hC : HolomorphicAt 3 (fun x : X => x.val j) p := by
    have h : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ) ∞ (fun w : X => w.val j) :=
      (EuclideanSpace.proj j : ComplexModel 3 →L[ℂ] ℂ).contMDiff.comp
      (contMDiff_subtype_val (U := productOpen U))
    exact Eventually.of_forall fun x =>
      (h.contMDiffAt (x := x)).mdifferentiableAt (by simp)
  have hp : p.val = 0 := map_zero (tangentInclusion 2 1)
  have hv : VanishesToOrderOn 3 record.N p 1 (fun x : X => x.val j) :=
    (vanishesToOrderOn_one_iff hx.1 hC).mpr (by rw [hp]; rfl)
  by_cases hj : j = 1
  · simp only [hj, if_true]
    have ht : VanishesToOrderOn 3 record.N p 3 (fun x : X => x.val (1 : Fin 3) ^ 3) := by
      subst j
      simpa only [pow_succ, pow_zero, one_mul] using (hv.mul hv).mul hv
    exact ht.mono (by decide)
  · simpa only [hj, if_false, pow_two] using hv.mul hv

/-- The positive order-one run starts at the actual nonempty canonical endpoint. -/
theorem order_run_restarts : regimeRun (OrdRegime record 1) B q = 0 := by
  have hn : ¬ OrdRegime record 1 (.refl (X := X)) (π q) := by
    rintro ⟨hc, he⟩
    have h := source_order_ge_two (π q) hc
    change nmOrd record (π q) = 1 at he
    omega
  exact regimeRun_step_of_not _ _ _ _ _ hn

/-- The actual successor reader uses the positive order-one companion
at the restarted head and the empty tail. -/
theorem actual_order_one_read :
    PositiveOrderCompanionWitness (k := 2) (by decide : 0 < 3) record B q 1
      (fun v => (invFamily (by decide : 0 < 3) 3).inv record B q = v) :=
  original_positive_order_successor_read (by decide : 0 < 3) record domain
    B (canonical _) q survivor 1 stage_nonmonomial_order (by decide)

open HironakaG1InitialPositiveGeneralRead MarkedIdealBiholomorphism BoundaryCount
  HomogenizedIdealAlong CoefficientIdeal MemberInterLocusAlong HomogenizedGlueingTower HironakaG1PositiveNormalNonspecialExample

private abbrev W := ordMask (M := Y) A 1
private abbrev V := CMfd.of (n := 3) W
private abbrev J : MarkedIdeal 3 V := compAt record 1 B
private abbrev R : BlowupTower V V := .refl

private theorem J_boundary :
    J.E = [(Subtype.val : W → Y) ⁻¹' F] := by
  have hE : A.E = [F] := by rw [show F = A.E.head! from rfl, stage_boundary]; rfl
  simp only [J, compAt, companionOf, companionAlong_E]
  change A.E.map ((Subtype.val : W → Y) ⁻¹' ·) = _
  rw [hE]
  rfl

private theorem J_level (hq : q ∈ W) :
    level J R (⟨q, hq⟩ : W) = 1 := by
  have hqF : q ∈ F := (born_iff chart_q.1).mpr (by change yChart.toFun q 1 = 0; rw [chart_q.2]; rfl)
  change boundaryCount (J.E.take J.E.length) (⟨q, hq⟩ : W) = _
  rw [List.take_length, J_boundary]
  simp [boundaryCount, show (⟨q, hq⟩ : W) ∈ (Subtype.val : W → Y) ⁻¹' F from hqF]

/-- The original value reads the literal companion at the endpoint, with
an empty recursive tail and one original slot in that companion. -/
theorem actual_positive_companion_level :
    ∃ hq : q ∈ W,
      let z : W := ⟨q, hq⟩
      IsInvDomain 3 J ∧ z ∈ J.cosupp ∧ level J R z = 1 ∧
      (invFamily (by decide : 0 < 3) 3).inv record B q =
        positiveSuccessorRead 1
          (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) J R z) := by
  let P (r : ℕ) : Prop :=
    let H := head B r
    let S := tail B r
    let O := ordMask (geoTransformAlong record H) 1
    let K := compAt record 1 H
    ∃ hp : S.proj q ∈ O,
      let T := restrict O S
      let z : openPreimage S O := ⟨q, hp⟩
      IsInvDomain 3 K ∧ IsMaximalOrderAlong K.N K.ideal K.d ∧
      IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) K) T ∧
      z ∈ (geoTransformAlong K T).cosupp ∧
      (invFamily (by decide : 0 < 3) 3).inv record B q =
        positiveSuccessorRead 1
          (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) K T z)
  have h : P 0 := order_run_restarts ▸ (show P (regimeRun (OrdRegime record 1) B q) from actual_order_one_read)
  obtain ⟨hq, hJ, _, _, hz, hRead⟩ := h
  exact ⟨hq, hJ, hz, J_level hq, hRead⟩

private theorem simple_not_ordGe {z : Y} (hz : z ∈ yChart.source)
    (he : coord 1 z = 0) (ha : coord 0 z ≠ 0) : z ∉ ordGe A 1 := by
  intro hzOrd
  have hd := isInvDomain_geoTransformAlong domain B test
  have hzF := (born_iff hz).mpr he
  have hzN := ordGe_subset_N A 1 hzOrd
  obtain ⟨k, hk⟩ := hd.isWellFormed.isClosedSubmanifold_N.2 z hzN
  obtain ⟨r, hr⟩ := exists_isLocalRetraction hk
  have hExp : 1 ≤ divExpAlong 3 A.N A.ideal F z :=
    (isDivNearAlong_iff_le_divExpAlong hr hzF (hd.isNonzeroAlongAt z hzN)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hd.isWellFormed.isCoherent hg)).mp (by
      filter_upwards [yChart.isOpen_source.mem_nhds hz] with w hw _ hwF
      exact (stage_cosupport_iff hw).mpr
        ((exceptionalCoordinate_coord w hw).trans ((born_iff hw).mp hwF)))
  have hE : A.E = [F] := by rw [show F = A.E.head! from rfl, stage_boundary]; rfl
  have hIdx : memberIdx A.E z = {0} := by
    ext i
    rw [hE, mem_memberIdx]
    simp [hzF]
  have hSum : 1 ≤ ∑ i ∈ memberIdx A.E z, expDataAlong 3 A.N A.ideal A.E z i := by
    rw [hIdx, Finset.sum_singleton]
    unfold expDataAlong
    simpa only [hE, List.length_singleton, Nat.zero_lt_one, dite_true, List.get_eq_getElem,
      List.getElem_singleton] using hExp
  have hRaw := (mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt hzN 1).mp hzOrd
  have hWhole := (whole_factor_order (by decide : 0 < 3) A hd.isWellFormed hd.isNonzeroAlongAt z hzN).1
  exact not_two_at_simple_point hz he ha (cosupport_anti (Nat.add_le_add hSum hRaw) hWhole)

private theorem J_mark : J.d = 1 := by
  simp only [J, compAt, companionOf, companionAlong_d]
  rfl

private theorem J_carrier : J.N = univ := by
  simp only [J, compAt, companionOf, companionAlong_N]
  change (Subtype.val : W → Y) ⁻¹' A.N = univ
  rw [stage_carrier, preimage_univ]

set_option maxHeartbeats 800000 in
private theorem J_nonspecial (hq : q ∈ W) (hJ : IsInvDomain 3 J) :
    ¬ IsSpecial J R (⟨q, hq⟩ : W) := by
  let z : W := ⟨q, hq⟩
  intro hSpecial
  rcases hSpecial with hZero | ⟨_, hMember⟩
  · exact (by decide : (1 : ℕ) ≠ 0) ((J_level hq).symm.trans hZero.1)
  have hBar : barMarked J = J := by
    change coeffMarkedAlong (homMarkedAlong J) = J
    rw [homMarkedAlong_eq_of_mark_one J J_mark hJ.isWellFormed.isCoherent,
      coeffMarkedAlong_eq_of_mark_one J J_mark hJ.isWellFormed.isCoherent]
  have hOrig : origMembers J R = J.E := List.take_length
  change z ∈ memberInterLocus (barMarked J).N (origMembers J R) (barMarked J).cosupp at hMember
  rw [hOrig, hBar, J_carrier, J_boundary] at hMember
  have hEv := (mem_memberInterLocus_iff.mp hMember).2
  have hEvW : ∀ᶠ u : W in 𝓝 z, u.val ∈ F → u ∈ J.cosupp := by
    filter_upwards [hEv] with u hu huF
    apply hu (mem_univ u)
    intro H hH _
    rw [List.mem_singleton.mp hH]
    exact huF
  have hMap : Filter.map (Subtype.val : W → Y) (𝓝 z) = 𝓝 q :=
    W.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq z
  have hEvY : ∀ᶠ w : Y in 𝓝 q, ∃ u : W, u.val = w ∧ (w ∈ F → u ∈ J.cosupp) := by
    rw [← hMap]
    exact hEvW.mono fun u hu => ⟨u, rfl, hu⟩
  obtain ⟨w, ⟨hw, he, ha⟩, u, hEq, hu⟩ := (frequently_simple_born.and_eventually hEvY).exists
  have huCos := hu ((born_iff hw).mpr he)
  let K : MarkedIdeal 3 V := MarkedIdeal.pullback (Subtype.val : W → Y) A
  have hA := isInvDomain_geoTransformAlong domain B test
  have hK : IsInvDomain 3 K := isInvDomain_pullback_val W hA
  have hBound : ∀ u ∈ K.cosupp, u ∉ ordGe K (1 + 1) := by
    intro u _ hu
    exact notMem_ordGe_of_mem_ordMask u.2
      ((mem_ordGe_pullback_val_iff (by decide : 0 < 3) hA.isWellFormed hA.isNonzeroAlongAt W 2 u).mp hu)
  have hCos := cosupp_companionOf_geoTransformAlong (by decide : 0 < 3) hK le_rfl hBound R trivial
  have huOrd : u ∈ ordGe K 1 := (show u ∈ ordGe K 1 ∩ K.cosupp from hCos ▸ huCos).1
  have hg := (mem_ordGe_pullback_val_iff (by decide : 0 < 3) hA.isWellFormed hA.isNonzeroAlongAt W 1 u).mp huOrd
  rw [hEq] at hg
  exact simple_not_ordGe hw he ha hg

set_option maxHeartbeats 800000 in
/-- The original successor value has a genuinely finite, level-one inner
Step One entry at the actual nonempty order-restart head. -/
theorem actual_finite_positive_companion :
    ∃ (hq : q ∈ W) (v : ValTy 2),
      let z : W := ⟨q, hq⟩
      J.d = 1 ∧ ¬ IsSpecial J R z ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) J R z =
        toLex (1, (v : WithTop (ValTy 2))) ∧
      (invFamily (by decide : 0 < 3) 3).inv record B q =
        positiveSuccessorRead 1 (toLex (1, (v : WithTop (ValTy 2)))) := by
  obtain ⟨hq, hJ, hz, hLevel, hRead⟩ := actual_positive_companion_level
  let z : W := ⟨q, hq⟩
  let R₂ := invFamily (by decide : 0 < 3) 2
  have hNS := J_nonspecial hq hJ
  have hBar : barMarked J = J := by
    change coeffMarkedAlong (homMarkedAlong J) = J
    rw [homMarkedAlong_eq_of_mark_one J J_mark hJ.isWellFormed.isCoherent,
      coeffMarkedAlong_eq_of_mark_one J J_mark hJ.isWellFormed.isCoherent]
  have hMax : IsMaximalOrderAlong J.N J.ideal J.d :=
    GeneralCompare.isMaximalOrderAlong_compAt (by decide : 0 < 3) 1 B
      (isInvDomain_geoTransformAlong domain B test)
  have hfin := Seq.StepOneValueMasked.lowerValueL_ne_top J R₂ hJ.isWellFormed hJ.one_le_d
    (by decide : 0 < 3) hMax (lowerMarkedM J) R trivial
    (show z ∈ (geoTransformAlong (barMarked J) R).cosupp from hBar.symm ▸ hz) hNS
  have hInner := Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R₂ J (lowerMarkedM J) R hNS
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hStep : Seq.StepOneValueMasked.stepOneInvM R₂ J R z = toLex (1, (v : WithTop (ValTy 2))) := by
    change Seq.StepOneValueMasked.stepOneInvL R₂ J (lowerMarkedM J) R z = _
    rw [hInner, ← hv, hLevel]
  exact ⟨hq, v, J_mark, hNS, hStep, hRead.trans (congrArg (positiveSuccessorRead 1) hStep)⟩

end
end Hironaka.HironakaG1RecursiveBornOrderExample
