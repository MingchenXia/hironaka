import Hironaka.Resolution.HironakaG1LaterPositiveSelectedExample

/-! The actual one-point controlled transform of the mark-one squared and cubed
coordinate ideal, with a born factor on its middle chart. -/
set_option autoImplicit false
namespace Hironaka.HironakaG1RecursiveBornFiniteExample

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

/-- The mark-one ideal of coordinate powers with no old boundary. -/
def record : MarkedIdeal 3 X :=
  ⟨univ, [], finiteFunctionIdeal sourceGen, 1⟩

private theorem record_coherent : record.ideal.IsCoherent :=
  isCoherent_finiteFunctionIdeal sourceGen sourceGen_mdifferentiable

private theorem sourceGen_mem (j : Fin 3) (z : X) :
    record.ideal.mem z (sourceGen j) :=
  isInSpanAt_self ⟨j, rfl⟩ (sourceGen_hol j z)

private theorem p_val : p.val = 0 := map_zero (tangentInclusion 2 1)

/-- The cosupport is the common coordinate origin, so the first centre is forced. -/
theorem initial_cosupport : record.cosupp = C := by
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

/-- The actual one-point blowup is canonical for every ordered invariant. -/
theorem canonical {Λ : Type} [LinearOrder Λ]
    (I : ∀ {Z : CMfd.{0} 3}, BlowupTower X Z → Z → Λ) :
    IsCanonical record I B := by
  refine ⟨trivial, Or.inr ?_⟩
  change C = ResolutionDriver.maxLocus (I (.refl : BlowupTower X X)) record.cosupp
  rw [initial_cosupport]
  ext z
  exact ⟨fun hz => ⟨hz, fun w hw => by rw [mem_singleton_iff.mp hz, mem_singleton_iff.mp hw]⟩,
    fun hz => hz.1⟩

/-- The generators in the controlled chart are the exceptional coordinate
times the squared first and third ratios and the middle coordinate. -/
def quotientGen (j : Fin 3) (z : Y) : ℂ :=
  exceptionalCoordinate z * (if j = 1 then yChart.toFun z j else yChart.toFun z j ^ 2)

private theorem quotientGen_hol (j : Fin 3) {z : Y} (hz : z ∈ yChart.source) :
    HolomorphicAt 3 (quotientGen j) z := by
  have he : exceptionalCoordinate =ᶠ[𝓝 z] fun w => yChart.toFun w (1 : Fin 3) := by
    filter_upwards [yChart.isOpen_source.mem_nhds hz] with w hw
    exact exceptionalCoordinate_coord w hw
  have h : HolomorphicAt 3 exceptionalCoordinate z := by
    filter_upwards [he.eventually_nhds, yChart.holomorphicAt_coord hz 1] with w hEq hw
    exact hw.congr_of_eventuallyEq (Filter.EventuallyEq.symm hEq)
  unfold quotientGen
  split
  · exact h.mul (yChart.holomorphicAt_coord hz j)
  · simp only [pow_two]
    exact h.mul ((yChart.holomorphicAt_coord hz j).mul (yChart.holomorphicAt_coord hz j))

private theorem generator_divides (j : Fin 3) {z : Y} (hz : z ∈ yChart.source) :
    (sourceGen j ∘ π) =ᶠ[𝓝 z] fun w => exceptionalCoordinate w * quotientGen j w := by
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
theorem quotientGen_mem (j : Fin 3) {z : Y} (hz : z ∈ yChart.source) :
    (controlledTransform hπ record.ideal 1).mem z (quotientGen j) := by
  refine mem_controlledTransform_of_eq_pow_mul
    HironakaG1LaterPositiveSelectedExample.equation_on_chart hz
    (sourceGen_mem j (π z)) (quotientGen_hol j hz) ?_
  simpa only [pow_one] using generator_divides j hz

/-- Every controlled germ on the middle chart is in the span of the three
displayed generators. -/
theorem controlled_span {z : Y} (hz : z ∈ yChart.source) {g : Y → ℂ}
    (hg : (controlledTransform hπ record.ideal 1).mem z g) :
    IsInSpanAt (n := 3) (fun b => ∃ j, b = quotientGen j) z g := by
  have hLambda : (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal.mem z
      exceptionalCoordinate := by
    change (GermIdeal.pullback (m := 3) π (vanishingIdeal (n := 3) C)).mem z
      (yChart.τ yChart.j ∘ π)
    exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self
      ⟨yChart.τ yChart.j, yChart.τ_mem_vanishingIdeal hz.1 yChart.hj, rfl⟩
      (holomorphicAt_comp_blowupProj (yChart.holomorphicAt_τ yChart.j hz.1)))
  have hLambda1 : (idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal 1).mem z
      exceptionalCoordinate := by
    rw [BlowupStrictIdeal.idealPow_one_exceptionalDivisor hπ]
    exact hLambda
  have hPB := (mem_colon_iff.mp hg).2 _ hLambda1
  have hSpan : IsInSpanAt (n := 3) (fun b => ∃ j, b = sourceGen j ∘ π) z
      (exceptionalCoordinate * g) := by
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
  have hCancel : ∀ᶠ w in 𝓝 z, exceptionalCoordinate w * g w = exceptionalCoordinate w * G w := by
    filter_upwards [he, eventually_all.mpr (fun l => generator_divides (j l) hz)] with w hw hwDiv
    change exceptionalCoordinate w * g w = ∑ l, b l w * s l w at hw
    rw [hw, show G w = ∑ l, b l w * quotientGen (j l) w from rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hj l, hwDiv l]
    ring
  exact ⟨(mem_colon_iff.mp hg).1, k, (fun l => quotientGen (j l)), b,
    (fun l => ⟨j l, rfl⟩), hb,
    eventuallyEq_of_mul_eventuallyEq yChart.isOpen_source exceptionalCoordinate_nontrivial hz
      (mem_colon_iff.mp hg).1 hG hCancel⟩

open HironakaPrincipalizationBoundary DivisorExponentAlong BlowupStrictSubmanifold
  InvDomainTowerAlong GermIdealTotalTransform HironakaAdmissibleSequence HironakaOneDimensionalCanonicalSuperlevels

/-- The concrete initial record lies in the invariant domain with empty boundary. -/
theorem domain : IsInvDomain 3 record := by
  refine isInvDomain_univ_of_isSNCDivisor record_coherent
    (fun z => isNonzeroAlongAt_univ_iff_exists.mpr ?_) isSNCDivisor_nil
  refine ⟨sourceGen 0, sourceGen_mem 0 z, ?_⟩
  intro hzero
  have hi := (productOpen U).isOpen.isOpenEmbedding_subtypeVal
  have hImage := hi.isOpenMap.image_mem_nhds hzero
  obtain ⟨_, ⟨w, hw, rfl⟩, hn⟩ := exists_coord_ne_zero_of_mem_nhds hImage (0 : Fin 3)
  have hwz : sourceGen 0 w = 0 := not_ne_iff.mp hw
  exact hn (eq_zero_of_pow_eq_zero hwz)

/-- The actual blowup is admissible for the new initial record. -/
theorem test : IsGeoTestTower record B :=
  ⟨trivial, (PointSupportedIdealPrincipalization.singleton_geometry_and_coherence (n := 3) p).1,
    initial_cosupport.ge, hasNormalCrossings_singleton p isSNCDivisor_nil⟩

/-- The transformed marked ideal retains the whole ambient carrier. -/
theorem stage_carrier : (geoTransformAlong record B).N = univ := by
  change geoStrictTransform π C univ = univ
  exact geoStrictTransform_univ hπ

/-- On the actual middle chart, the transformed ideal is exactly the span
of the displayed generators. -/
theorem stage_span {z : Y} (hz : z ∈ yChart.source) (g : Y → ℂ) :
    (geoTransformAlong record B).ideal.mem z g ↔
      IsInSpanAt (n := 3) (fun b => ∃ j, b = quotientGen j) z g := by
  have hI : (geoTransformAlong record B).ideal = controlledTransform hπ record.ideal 1 :=
    geoTransform_ideal_eq_controlledTransform (𝔪 := record) rfl record_coherent hπ
  rw [hI]
  refine ⟨controlled_span hz, fun hg => ?_⟩
  rw [← hI]
  refine mem_of_isInSpanAt_mem (isInvDomain_geoTransformAlong domain B test).isWellFormed.isCoherent
    (hg.mono ?_)
  rintro _ ⟨j, rfl⟩
  rw [hI]
  exact quotientGen_mem j hz

/-- The endpoint cosupport is precisely the born divisor on this chart. -/
theorem stage_cosupport_iff {z : Y} (hz : z ∈ yChart.source) :
    z ∈ (geoTransformAlong record B).cosupp ↔ exceptionalCoordinate z = 0 := by
  have hd := (isInvDomain_geoTransformAlong domain B test).isWellFormed.isCoherent
  constructor
  · intro h
    have hg := (stage_span hz (quotientGen 1)).mpr
      (isInSpanAt_self ⟨1, rfl⟩ (quotientGen_hol 1 hz))
    have hv := (vanishesToOrderOn_one_iff h.1
      (GermIdeal.IsCoherent.holomorphicAt_mem hd hg)).mp (h.2 _ hg)
    have he := exceptionalCoordinate_coord z hz
    exact eq_zero_of_mul_self_eq_zero (by simpa [quotientGen, ← he] using hv)
  · intro he
    have hzN : z ∈ (geoTransformAlong record B).N := stage_carrier.symm ▸ mem_univ z
    refine ⟨hzN, fun g hg => ?_⟩
    refine (vanishesToOrderOn_one_iff hzN
      (GermIdeal.IsCoherent.holomorphicAt_mem hd hg)).mpr ?_
    obtain ⟨_, k, s, b, hs, _, heq⟩ := (stage_span hz g).mp hg
    rw [heq.self_of_nhds]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨j, hj⟩ := hs i
    rw [hj, quotientGen, he, zero_mul, mul_zero]

/-- The origin of the actual middle chart survives the canonical blowup. -/
theorem survivor : q ∈ (geoTransformAlong record B).cosupp :=
  (stage_cosupport_iff chart_q.1).mpr (by rw [exceptionalCoordinate_coord q chart_q.1, chart_q.2]; rfl)

end
end Hironaka.HironakaG1RecursiveBornFiniteExample
