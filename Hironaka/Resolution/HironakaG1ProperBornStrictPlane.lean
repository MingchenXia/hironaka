import Hironaka.Resolution.HironakaG1ProperCarrierNormalContact
import Hironaka.Resolution.HironakaG1LaterPositiveNormalExample
import Hironaka.Resolution.HironakaG1RecursiveBornOrderExample

/-! The actual strict zero-plane carrier in the middle chart of the point blowup. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1ProperBornStrictPlane

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold HironakaActualOpenZeroSectionDifferentials HironakaG1LaterPositiveNormalExample
  GermIdealOrder MonomialPartEtale IdealWeightPowers

noncomputable section

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev C : Set X := {p}

/-- The literal closed plane transverse to the third coordinate. -/
def plane : Set X := {x | x.val (2 : Fin 3) = 0}

/-- Its actual strict transform under the point blowup. -/
def strictPlane : Set Y := geoStrictTransform π C plane

private abbrev coord (i : Fin 3) (z : Y) := yChart.toFun z i

private theorem p_val : p.val = 0 := by simp [p, zeroSection]

private theorem offCentre_iff_middle {z : Y} (hz : z ∈ yChart.source) :
    π z ∉ C ↔ coord 1 z ≠ 0 := by
  suffices h : π z ∈ C ↔ coord 1 z = 0 by exact not_congr h
  constructor
  · intro h
    have h' := congrArg (fun x : X => x.val (1 : Fin 3)) (mem_singleton_iff.mp h)
    change (π z).val (1 : Fin 3) = p.val (1 : Fin 3) at h'
    rw [chart_projection z hz,p_val,monomial_apply] at h'
    simpa using h'
  · intro h
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    rw [chart_projection z hz,p_val]
    ext i
    by_cases hi : i = 1
    · subst i
      simpa [monomial_apply] using h
    · simp [monomial_apply,hi,h]

private theorem source_plane_iff {z : Y} (hz : z ∈ yChart.source) (h : coord 1 z ≠ 0) :
    π z ∈ plane ↔ coord 2 z = 0 := by
  change (π z).val (2 : Fin 3) = 0 ↔ _
  rw [chart_projection z hz,monomial_apply]
  simp [show (2 : Fin 3) ≠ 1 by decide, mul_eq_zero, h]

private def axis (a : ℂ) : ComplexModel 3 :=
  a • EuclideanSpace.single (1 : Fin 3) (1 : ℂ)

private theorem axis_coord (a : ℂ) (i : Fin 3) :
    axis a i = if i = 1 then a else 0 := by
  by_cases h : i = 1 <;> simp [axis,h]

/-- The strict carrier in the literal middle chart is exactly the
third-coordinate plane, including on the born divisor. -/
theorem strictPlane_iff_middle_chart {z : Y} (hz : z ∈ yChart.source) :
    z ∈ strictPlane ↔ coord 2 z = 0 := by
  constructor
  · intro h
    have hFreq : ∃ᶠ w in 𝓝 z, π w ∈ plane ∧ π w ∉ C :=
      mem_closure_iff_frequently.mp h
    by_contra hn
    have hcont : ContinuousAt (coord 2) z :=
      (yChart.holomorphicAt_coord hz 2).self_of_nhds.continuousAt
    have hne : ∀ᶠ w in 𝓝 z, coord 2 w ≠ 0 := hcont.eventually_ne hn
    have hSource : ∀ᶠ w in 𝓝 z, w ∈ yChart.source := yChart.isOpen_source.mem_nhds hz
    obtain ⟨w, ⟨hw, hwC⟩, hwS, hwNe⟩ :=
      (hFreq.and_eventually (hSource.and hne)).exists
    exact hwNe ((source_plane_iff hwS ((offCentre_iff_middle hwS).mp hwC)).mp hw)
  · intro h
    by_cases hm : coord 1 z = 0
    · let γ : ℂ → Y := fun a => yChart.invFun (yChart.toFun z + axis a)
      have hAxis : Continuous axis := continuous_id.smul continuous_const
      have hAxis0 : axis 0 = 0 := by simp [axis]
      have hInput : Tendsto (fun a => yChart.toFun z + axis a) (𝓝 0) (𝓝 (yChart.toFun z)) := by
        simpa [Pi.add_def,hAxis0] using (continuous_const.add hAxis).tendsto (0 : ℂ)
      have hi := yChart.homeo.tendsto_symm (x := z) hz
      have hγ : Tendsto γ (𝓝 0) (𝓝 z) := hi.comp hInput
      have hne : ∃ᶠ a : ℂ in 𝓝 0, a ≠ 0 := by
        have hF : ∃ᶠ a : ℂ in 𝓝[≠] 0, True := (Eventually.of_forall fun _ => trivial).frequently
        exact ((frequently_nhdsWithin_iff).mp hF).mono (fun _ ha => ha.2)
      apply mem_closure_iff_frequently.mpr
      exact hγ.frequently (hne.mono fun a ha => by
        let w := yChart.toFun z + axis a
        have hS : γ a ∈ yChart.source := yChart.toPartialEquiv.map_target (chart_all w)
        have hChart : yChart.toFun (γ a) = w := yChart.toPartialEquiv.right_inv (chart_all w)
        have h1 : coord 1 (γ a) ≠ 0 := by
          change yChart.toFun (γ a) 1 ≠ 0
          rw [hChart]
          change coord 1 z + axis a 1 ≠ 0
          simpa [hm,axis_coord] using ha
        have h2 : coord 2 (γ a) = 0 := by
          change yChart.toFun (γ a) 2 = 0
          rw [hChart]
          change coord 2 z + axis a 2 = 0
          simp [h,axis_coord,show (2 : Fin 3) ≠ 1 by decide]
        exact ⟨(source_plane_iff hS h1).mpr h2, (offCentre_iff_middle hS).mpr h1⟩)
    · exact subset_closure ⟨(source_plane_iff hz hm).mpr h,(offCentre_iff_middle hz).mpr hm⟩

open HomogenizedEquivalence GermOrderProduct MonomialCase CompanionReduction OrderTaylor

private def chart : ComplexChart 3 Y :=
  ⟨yChart.homeo, atlasHomeo_mem_atlas yChart.toPartialEquiv (Or.inl ⟨yChart, rfl⟩)⟩

/-- The horizontal controlled generator has exact order one on the actual
strict plane at every point with middle coordinate zero and first coordinate nonzero. -/
theorem horizontal_order_one_on_strictPlane {z : Y}
    (hz : z ∈ yChart.source) (hs : z ∈ strictPlane) (he : coord 1 z = 0)
    (ha : coord 0 z ≠ 0) :
    VanishesToOrderOn 3 strictPlane z 1 (fun w => coord 1 w * coord 0 w ^ 3) ∧
      ¬ VanishesToOrderOn 3 strictPlane z 2 (fun w => coord 1 w * coord 0 w ^ 3) := by
  have h0 : HolomorphicAt 3 (coord 0) z := yChart.holomorphicAt_coord hz 0
  have h1 : HolomorphicAt 3 (coord 1) z := yChart.holomorphicAt_coord hz 1
  have hHol := h1.mul (holomorphicAt_pow_of h0 3)
  refine ⟨(vanishesToOrderOn_one_iff hs hHol).mpr (by simp [he]), ?_⟩
  let θ : ComplexModel 3 → Y := fun w => yChart.invFun (yChart.toFun z + axis (w 1))
  have hAt : θ 0 = z := by
    simpa [θ,axis] using yChart.toPartialEquiv.left_inv hz
  have hDiff : ∀ᶠ w : ComplexModel 3 in 𝓝 0,
      MDifferentiableAt 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) θ w :=
    Eventually.of_forall fun w => by
      have hProj : MDifferentiableAt 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ)
          (fun v => v (1 : Fin 3)) w :=
        (EuclideanSpace.proj (1 : Fin 3) : ComplexModel 3 →L[ℂ] ℂ).mdifferentiableAt
      have hVector : MDifferentiableAt 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3)
          (fun _ => EuclideanSpace.single (1 : Fin 3) (1 : ℂ)) w := mdifferentiableAt_const
      have hInput : MDifferentiableAt 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3)
          (fun v => yChart.toFun z + axis (v 1)) w :=
        mdifferentiableAt_const.add (hProj.smul hVector)
      exact (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel 3)) chart.property
        (chart_all (yChart.toFun z + axis (w 1)))).comp w hInput
  have hCoord (w : ComplexModel 3) (i : Fin 3) :
      coord i (θ w) = coord i z + if i = 1 then w 1 else 0 := by
    change yChart.toFun (yChart.invFun (yChart.toFun z + axis (w 1))) i = _
    have hr : yChart.toFun (yChart.invFun (yChart.toFun z + axis (w 1))) =
        yChart.toFun z + axis (w 1) :=
      yChart.toPartialEquiv.right_inv (chart_all _)
    rw [hr]
    change coord i z + axis (w 1) i = _
    rw [axis_coord]
  have hPlane (w : ComplexModel 3) : θ w ∈ strictPlane :=
    (strictPlane_iff_middle_chart (yChart.toPartialEquiv.map_target (chart_all _))).mpr (by
      change coord 2 (θ w) = 0
      rw [hCoord]
      simpa using (strictPlane_iff_middle_chart hz).mp hs)
  intro h
  obtain ⟨b, hb, hEq⟩ := vanishesToOrderOn_comp (θ := θ) (p := (0 : ComplexModel 3))
    hDiff (hAt.symm ▸ h)
  have hSame : (fun w : ComplexModel 3 => w (1 : Fin 3) * coord 0 z ^ 3) =ᶠ[𝓝 0] b := by
    filter_upwards [hEq] with w hw
    simpa [hCoord,he,show (0 : Fin 3) ≠ 1 by decide] using (hw (hPlane w))
  let Φ : LocalHolomorphicEquivAt (n := 3) (chartAt (ComplexModel 3) (0 : ComplexModel 3) 0) :=
    BlowupExistenceOriginIdeal.idEquivAt
  have hLinear := flatCoord_notMem_idealPow_two Φ 1 (mem_flatDomain_self Φ)
  have hConst : ¬ (idealPow (pointIdeal 3 (0 : ComplexModel 3)) 1).mem 0
      (fun _ => coord 0 z ^ 3) :=
    fun hC => pow_ne_zero 3 ha (apply_eq_zero_of_mem_idealPow_pointIdeal (x := (0 : ComplexModel 3)) le_rfl hC)
  exact mul_notMem_idealPow (a := 1) (b := 0)
    (Eventually.of_forall
      fun _ => (EuclideanSpace.proj (1 : Fin 3) : ComplexModel 3 →L[ℂ] ℂ).mdifferentiableAt)
    (holomorphicAt_const (coord 0 z ^ 3)) hLinear hConst (mem_idealPow_congr hb hSame.symm)

open MarkedIdeals MarkedIdeals.MarkedIdeal RelativePrincipalizationSpan
  GermIdealPullbackCalculus InvertibleIdealQuotient BlowupControlledTransform
  BlowupFunctionTransform HironakaActualCoherentWeightedCoefficientMarked HironakaG8LogClosureHistory

def sourceGen (j : Fin 3) (z : X) : ℂ :=
  z.val j ^ (if j = 1 then 4 else if j = 2 then 2 else 3)

private theorem sourceGen_mdifferentiable (j : Fin 3) : MDifferentiable 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ) (sourceGen j) := by
  have h : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ) ∞
      (fun w : X => w.val j) :=
    (EuclideanSpace.proj j : ComplexModel 3 →L[ℂ] ℂ).contMDiff.comp contMDiff_subtype_val
  exact fun z => (h.contMDiffAt (x := z)).mdifferentiableAt (by simp) |>.pow _

private theorem sourceGen_hol (j : Fin 3) (z : X) : HolomorphicAt 3 (sourceGen j) z :=
  Eventually.of_forall (sourceGen_mdifferentiable j)

/-- The whole coherent coordinate powers at the actual mark two. -/
def record : MarkedIdeal 3 X := ⟨univ, [], finiteFunctionIdeal sourceGen, 2⟩

private theorem record_coherent : record.ideal.IsCoherent :=
  isCoherent_finiteFunctionIdeal sourceGen sourceGen_mdifferentiable


private theorem sourceGen_mem (j : Fin 3) (z : X) :
    record.ideal.mem z (sourceGen j) :=
  isInSpanAt_self ⟨j, rfl⟩ (sourceGen_hol j z)


/-- The controlled generators in the middle chart are the exceptional coordinate times the first ratio cubed, the middle coordinate squared, and the normal ratio squared. -/
def quotientGen (j : Fin 3) (z : Y) : ℂ :=
  if j = 2 then coord j z ^ 2 else
    exceptionalCoordinate z * (if j = 1 then coord j z else coord j z ^ 3)

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
  · exact holomorphicAt_pow_of (yChart.holomorphicAt_coord hz j) 2
  split
  · exact hEx.mul (yChart.holomorphicAt_coord hz j)
  · exact hEx.mul (holomorphicAt_pow_of (yChart.holomorphicAt_coord hz j) 3)

private theorem generator_divides (j : Fin 3) {z : Y} (hz : z ∈ yChart.source) :
    (sourceGen j ∘ π) =ᶠ[𝓝 z] fun w => exceptionalCoordinate w ^ 2 * quotientGen j w := by
  filter_upwards [yChart.isOpen_source.mem_nhds hz] with w hw
  change (π w).val j ^ (if j = 1 then 4 else if j = 2 then 2 else 3) = _
  rw [chart_projection w hw, monomial_apply]
  unfold quotientGen
  rw [exceptionalCoordinate_coord w hw]
  by_cases hj : j = 1
  · subst j
    simp [show (1 : Fin 3) ≠ 2 by decide]
    ring
  · by_cases hk : j = 2
    · subst j
      simp [hj]
      ring
    · simp [hj,hk]
      ring

/-- Each of the explicit chart generators is in the actual controlled transform. -/
theorem quotientGen_mem (j : Fin 3) {z : Y} (hz : z ∈ yChart.source) :
    (controlledTransform hπ record.ideal 2).mem z (quotientGen j) := by
  refine mem_controlledTransform_of_eq_pow_mul
    HironakaG1LaterPositiveSelectedExample.equation_on_chart hz
    (sourceGen_mem j (π z)) (quotientGen_hol j hz) ?_
  exact generator_divides j hz

/-- Every controlled germ on the middle chart is in the span of the three
displayed generators. -/
theorem controlled_span {z : Y} (hz : z ∈ yChart.source) {g : Y → ℂ}
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

open IdealOrderArithmetic

private theorem exceptional_eq {z : Y} (hz : z ∈ yChart.source) :
    exceptionalCoordinate =ᶠ[𝓝 z] coord 1 := by
  filter_upwards [yChart.isOpen_source.mem_nhds hz] with w hw
  exact exceptionalCoordinate_coord w hw

private theorem vanishes_congr {x : Y} {f g : Y → ℂ} {k : ℕ}
    (h : f =ᶠ[𝓝 x] g) (hf : VanishesToOrderOn 3 strictPlane x k f) :
    VanishesToOrderOn 3 strictPlane x k g := by
  obtain ⟨b, hb, he⟩ := hf
  refine ⟨b, hb, ?_⟩
  filter_upwards [he, h] with w hw hfg hwN
  exact hfg.symm.trans (hw hwN)

/-- The middle chart origin survives on the strict plane at the original mark. -/
theorem strictPlane_survivor :
    q ∈ cosupport 3 strictPlane (controlledTransform hπ record.ideal 2) 2 := by
  have hCoord (i : Fin 3) : coord i q = 0 := by
    change yChart.toFun q i = 0
    rw [chart_q.2]
    rfl
  have hq : q ∈ strictPlane := (strictPlane_iff_middle_chart chart_q.1).mpr (hCoord 2)
  have hv (i : Fin 3) : VanishesToOrderOn 3 strictPlane q 1 (coord i) :=
    (vanishesToOrderOn_one_iff hq (yChart.holomorphicAt_coord chart_q.1 i)).mpr (hCoord i)
  refine ⟨hq, fun g hg => IsInSpanAt.vanishesToOrderOn (controlled_span chart_q.1 hg) ?_⟩
  rintro _ ⟨j, rfl⟩
  have hPow : VanishesToOrderOn 3 strictPlane q 3 (fun w => coord j w ^ 3) := by
    simpa [pow_succ] using ((hv j).mul (hv j)).mul (hv j)
  refine vanishes_congr ?_ (show VanishesToOrderOn 3 strictPlane q 2
    (fun w => if j = 2 then coord j w ^ 2 else
      coord 1 w * (if j = 1 then coord j w else coord j w ^ 3)) from ?_)
  · filter_upwards [exceptional_eq chart_q.1] with w hw
    unfold quotientGen
    rw [hw]
  · by_cases h2 : j = 2
    · simpa [h2,pow_two] using (hv j).mul (hv j)
    · by_cases h1 : j = 1
      · simpa [h2,h1] using (hv 1).mul (hv j)
      · simpa [h2,h1] using (hv 1).mul (hPow.mono (by decide : 1 ≤ 3))

/-- Along the smooth born trace away from the first-coordinate zero set,
the actual controlled ideal on the strict plane has order exactly one. -/
theorem strictPlane_born_order_one {z : Y} (hz : z ∈ yChart.source) (hs : z ∈ strictPlane)
    (he : coord 1 z = 0) (ha : coord 0 z ≠ 0) :
    z ∈ cosupport 3 strictPlane (controlledTransform hπ record.ideal 2) 1 ∧
      z ∉ cosupport 3 strictPlane (controlledTransform hπ record.ideal 2) 2 := by
  refine ⟨⟨hs, fun g hg => IsInSpanAt.vanishesToOrderOn (controlled_span hz hg) ?_⟩, ?_⟩
  · rintro _ ⟨j, rfl⟩
    apply (vanishesToOrderOn_one_iff hs (quotientGen_hol j hz)).mpr
    rw [quotientGen,exceptionalCoordinate_coord z hz]
    simp [he]
    intro hj
    subst j
    exact (strictPlane_iff_middle_chart hz).mp hs
  · intro h
    have hQ := h.2 _ (quotientGen_mem 0 hz)
    apply (horizontal_order_one_on_strictPlane hz hs he ha).2
    refine vanishes_congr ?_ hQ
    filter_upwards [exceptional_eq hz] with w hw
    unfold quotientGen
    rw [hw,if_neg (by decide : (0 : Fin 3) ≠ 2),if_neg (by decide : (0 : Fin 3) ≠ 1)]

open HironakaG1ProperCarrierNormalContact HironakaActualRelativeNormalGeometry
  HironakaActualZeroCoordinateContactSeed HironakaActualGraphFunctionalIdeal
  HironakaActualCentreJointJets TangentDirectionAlong

private theorem normal_eq (x : X) : relativeNormalCoordinate U x = x.val (2 : Fin 3) := by
  simp [relativeNormalCoordinate,addedCoordinate,graphFunction,zeroFunction]

/-- The closed carrier is the zero set of the actual mark-two tangent of
the whole coherent source ideal, supplied by its normal square generator. -/
theorem plane_tangent :
    plane = {x | relativeNormalCoordinate U x = 0} ∧
      IsTangentDirectionAlong record.N record.ideal record.d univ
        (relativeNormalCoordinate U) := by
  refine ⟨Set.ext (fun x => by simp [plane,normal_eq]), ?_⟩
  have hT := normal_tangent_of_power_member U univ record.ideal record_coherent 2 (by decide)
    (fun x => by
      have hGen : sourceGen 2 = fun z => relativeNormalCoordinate U z ^ 2 := by
        funext z
        simp [normal_eq,sourceGen,show (2 : Fin 3) ≠ 1 by decide]
      rw [← hGen]
      exact sourceGen_mem 2 x)
  simpa [record] using hT

/-- The order-one points of the true strict carrier on the born divisor
occur in every neighbourhood of the surviving point. -/
theorem frequently_strictPlane_born_order_one :
    ∃ᶠ z in 𝓝 q, π z = p ∧
      z ∈ cosupport 3 strictPlane (controlledTransform hπ record.ideal 2) 1 ∧
      z ∉ cosupport 3 strictPlane (controlledTransform hπ record.ideal 2) 2 := by
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
    have ht := chart_all (w a)
    have hz := yChart.toPartialEquiv.map_target ht
    have hr := yChart.toPartialEquiv.right_inv ht
    have hCoord (i : Fin 3) : coord i (yChart.invFun (w a)) = w a i :=
      congrArg (fun v : ComplexModel 3 => v i) hr
    have h1 : coord 1 (yChart.invFun (w a)) = 0 := by rw [hCoord]; simp [w]
    have h2 : coord 2 (yChart.invFun (w a)) = 0 := by rw [hCoord]; simp [w]
    have h0 : coord 0 (yChart.invFun (w a)) ≠ 0 := by rw [hCoord]; simpa [w] using ha
    have hp : π (yChart.invFun (w a)) = p :=
      mem_singleton_iff.mp (by simpa using mt (offCentre_iff_middle hz).mp (not_not.mpr h1))
    exact ⟨hp, strictPlane_born_order_one hz ((strictPlane_iff_middle_chart hz).mpr h2) h1 h0⟩)

open DivisorExponentAlong

/-- The born exceptional fibre has submark exponent one on the actual
proper carrier, at the point surviving the mark-two control. -/
theorem strictPlane_born_exponent :
    divExpAlong 3 strictPlane (controlledTransform hπ record.ideal 2) (π ⁻¹' C) q = 1 := by
  classical
  have hDiv : IsDivNearAlong 3 strictPlane (controlledTransform hπ record.ideal 2) (π ⁻¹' C) 1 q := by
    filter_upwards [yChart.isOpen_source.mem_nhds chart_q.1] with z hz hs hf
    have h : coord 1 z = 0 := by
      by_contra hn
      exact (offCentre_iff_middle hz).mpr hn hf
    exact ⟨hs,fun g hg => IsInSpanAt.vanishesToOrderOn (controlled_span hz hg) (by
      rintro _ ⟨j,rfl⟩
      apply (vanishesToOrderOn_one_iff hs (quotientGen_hol j hz)).mpr
      unfold quotientGen
      have hz0 : exceptionalCoordinate z = 0 := (exceptionalCoordinate_coord z hz).trans h
      rw [hz0,zero_mul]
      split
      · rename_i hj
        subst j
        rw [(strictPlane_iff_middle_chart hz).mp hs,zero_pow (by decide : 2 ≠ 0)]
      · rfl)⟩
  have hNot : ¬ IsDivNearAlong 3 strictPlane (controlledTransform hπ record.ideal 2) (π ⁻¹' C) 2 q := by
    intro h
    obtain ⟨z,⟨hp,hz,hn⟩,hd⟩ := (frequently_strictPlane_born_order_one.and_eventually h).exists
    exact hn (hd hz.1 (mem_singleton_iff.mpr hp))
  have hex : ∃ e, ¬ IsDivNearAlong 3 strictPlane (controlledTransform hπ record.ideal 2)
      (π ⁻¹' C) (e + 1) q := ⟨1,hNot⟩
  rw [divExpAlong,dif_pos hex]
  exact le_antisymm (Nat.find_min' hex hNot) (by
    by_contra! h
    have he : Nat.find hex = 0 := by omega
    exact Nat.find_spec hex (by simpa [he] using hDiv))

#print axioms strictPlane_born_exponent
#print axioms frequently_strictPlane_born_order_one
#print axioms plane_tangent
#print axioms strictPlane_survivor
#print axioms strictPlane_born_order_one
#print axioms quotientGen_mem
#print axioms controlled_span
#print axioms strictPlane_iff_middle_chart
#print axioms horizontal_order_one_on_strictPlane

end
end Hironaka.HironakaG1ProperBornStrictPlane
