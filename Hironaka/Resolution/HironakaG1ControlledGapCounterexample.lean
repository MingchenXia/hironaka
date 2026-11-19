import Hironaka.Resolution.HironakaG1RecursiveBornOrderExample
import Hironaka.Resolution.HironakaG8GapNormalizedExponent

/-! An actual admissible point blowup can lose the ordinary cosupport gap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Hironaka.HironakaG1ControlledGapCounterexample

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
  z.val j ^ (if j = 1 then 3 else 2)

private theorem sourceGen_mdifferentiable (j : Fin 3) : MDifferentiable 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ) (sourceGen j) := by
  have h : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ) ∞
      (fun w : X => w.val j) :=
    (EuclideanSpace.proj j : ComplexModel 3 →L[ℂ] ℂ).contMDiff.comp contMDiff_subtype_val
  exact fun z => (h.contMDiffAt (x := z)).mdifferentiableAt (by simp) |>.pow _

private theorem sourceGen_hol (j : Fin 3) (z : X) : HolomorphicAt 3 (sourceGen j) z :=
  Eventually.of_forall (sourceGen_mdifferentiable j)

open HironakaG1RecursiveBornFiniteExample

private theorem sourceGen_mem (j : Fin 3) (z : X) :
    HironakaG1RecursiveBornFiniteExample.record.ideal.mem z (sourceGen j) :=
  isInSpanAt_self ⟨j, rfl⟩ (sourceGen_hol j z)

private theorem p_val : p.val = 0 := map_zero (tangentInclusion 2 1)

/-- The generators in the controlled chart are the squared first and third ratios and the linear middle coordinate. -/
private def quotientGen (j : Fin 3) (z : Y) : ℂ :=
  if j = 1 then yChart.toFun z j else yChart.toFun z j ^ 2

private theorem quotientGen_hol (j : Fin 3) {z : Y} (hz : z ∈ yChart.source) :
    HolomorphicAt 3 (quotientGen j) z := by
  unfold quotientGen
  split
  · exact yChart.holomorphicAt_coord hz j
  · simp only [pow_two]
    exact (yChart.holomorphicAt_coord hz j).mul (yChart.holomorphicAt_coord hz j)

private theorem generator_divides (j : Fin 3) {z : Y} (hz : z ∈ yChart.source) :
    (sourceGen j ∘ π) =ᶠ[𝓝 z] fun w => exceptionalCoordinate w ^ 2 * quotientGen j w := by
  filter_upwards [yChart.isOpen_source.mem_nhds hz] with w hw
  change (π w).val j ^ (if j = 1 then 3 else 2) = _
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

/-- The whole coherent source ideal of actual coordinate squares and a
cube, at mark two. Its original (empty) boundary and whole carrier are
the same as in the original point example. -/
def raisedRecord : MarkedIdeal 3 X := {record with d := 2}

private theorem raised_domain : IsInvDomain 3 raisedRecord :=
  ⟨⟨domain.isWellFormed.isClosedSubmanifold_N, domain.isWellFormed.isCoherent,
      domain.isWellFormed.isSNCDivisor, domain.isWellFormed.isTransverse⟩, domain.dimLE,
    by decide, domain.isNonzeroAlongAt⟩

private theorem raised_gap : HasCosupportGap raisedRecord := by
  intro x hx hx₁
  have hBase : record.cosupp = ({p} : Set X) := initial_cosupport
  have he : x = p := mem_singleton_iff.mp (hBase ▸ (show x ∈ record.cosupp from hx₁))
  subst x
  refine ⟨hx, fun g hg => ?_⟩
  change record.ideal.mem p g at hg
  unfold record at hg
  refine IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn hg ?_
  rintro _ ⟨j,rfl⟩
  change VanishesToOrderOn 3 raisedRecord.N p 2 (sourceGen j)
  have hC : HolomorphicAt 3 (fun x : X => x.val j) p := by
    have h : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ) ∞ (fun w : X => w.val j) :=
      (EuclideanSpace.proj j : ComplexModel 3 →L[ℂ] ℂ).contMDiff.comp contMDiff_subtype_val
    exact Eventually.of_forall fun x => (h.contMDiffAt (x := x)).mdifferentiableAt (by simp)
  have hv : VanishesToOrderOn 3 raisedRecord.N p 1 (fun x : X => x.val j) :=
    (vanishesToOrderOn_one_iff hx hC).mpr (by rw [p_val]; rfl)
  by_cases hj : j = 1
  · subst j
    have hCubed : VanishesToOrderOn 3 raisedRecord.N p 3 (fun x : X => x.val (1 : Fin 3) ^ 3) := by
      simpa only [pow_succ, pow_zero, one_mul] using (hv.mul hv).mul hv
    change VanishesToOrderOn 3 raisedRecord.N p 2 (fun x => x.val (1 : Fin 3) ^ 3)
    exact hCubed.mono (by decide : 2 ≤ 3)
  · have he : sourceGen j = fun x : X => x.val j * x.val j := by
      funext x
      unfold sourceGen
      rw [if_neg hj,pow_two]
    rw [he]
    exact hv.mul hv

private theorem raised_cosupp : raisedRecord.cosupp = {p} := by
  rw [← show record.cosupp = ({p} : Set X) from initial_cosupport]
  exact subset_antisymm (cosupport_anti (by decide : 1 ≤ 2))
    (fun x hx => raised_gap x hx.1 hx)

private theorem raised_test : IsGeoTestTower raisedRecord B :=
  ⟨trivial, (PointSupportedIdealPrincipalization.singleton_geometry_and_coherence (n := 3) p).1,
    raised_cosupp.ge, hasNormalCrossings_singleton p isSNCDivisor_nil⟩

private theorem raised_canonical {Λ : Type} [LinearOrder Λ]
    (I : ∀ {Z : CMfd.{0} 3}, BlowupTower X Z → Z → Λ) : IsCanonical raisedRecord I B := by
  refine ⟨trivial, Or.inr ?_⟩
  change {p} = ResolutionDriver.maxLocus (I (.refl : BlowupTower X X)) raisedRecord.cosupp
  rw [raised_cosupp]
  ext z
  exact ⟨fun hz => ⟨hz, fun w hw => by rw [mem_singleton_iff.mp hz, mem_singleton_iff.mp hw]⟩,
    fun hz => hz.1⟩

/-- A genuinely canonical admissible blowup of a marked record with
source gap can leave ordinary order one at a mark-two endpoint.
Consequently the advanced gap cannot follow from controlled tests or
canonicity and the source gap alone. -/
theorem canonical_point_blowup_loses_gap :
    IsInvDomain 3 raisedRecord ∧ HasCosupportGap raisedRecord ∧
      IsGeoTestTower raisedRecord B ∧
      IsCanonical raisedRecord ((invFamily (by decide : 0 < 3) 3).inv raisedRecord) B ∧
      ¬ HasCosupportGap (geoTransformAlong raisedRecord B) := by
  refine ⟨raised_domain,raised_gap,raised_test,raised_canonical _,?_⟩
  let A := geoTransformAlong raisedRecord B
  have hN : A.N = univ := stage_carrier
  have hI : A.ideal = controlledTransform hπ record.ideal 2 :=
    geoTransform_ideal_eq_controlledTransform (𝔪 := raisedRecord) rfl
      raised_domain.isWellFormed.isCoherent hπ
  have hqN : q ∈ A.N := hN.symm ▸ mem_univ _
  have hq1 : q ∈ cosupport 3 A.N A.ideal 1 := by
    refine ⟨hqN, fun g hg => ?_⟩
    have hg' := controlled_span chart_q.1 (hI ▸ hg)
    apply IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn hg'
    rintro _ ⟨j,rfl⟩
    refine (vanishesToOrderOn_one_iff hqN (quotientGen_hol j chart_q.1)).mpr ?_
    simp [quotientGen,chart_q.2]
  have hq2 : q ∉ A.cosupp := by
    intro hq
    have hm : A.ideal.mem q (quotientGen 1) := hI.symm ▸ quotientGen_mem 1 chart_q.1
    have hv : VanishesToOrderOn 3 A.N q 2 (coord 1) := by
      have he : quotientGen 1 = coord 1 := by funext z; unfold quotientGen; rw [if_pos rfl]
      rw [← he]
      exact hq.2 _ hm
    exact point_not_two chart_q.1 (by change yChart.toFun q 1 = 0; rw [chart_q.2]; rfl)
      (mem_idealPow_of_vanishesToOrderOn_univ (hN ▸ hv))
  exact fun hGap => hq2 (hGap q hqN hq1)

#print axioms canonical_point_blowup_loses_gap

end
end Hironaka.HironakaG1ControlledGapCounterexample
