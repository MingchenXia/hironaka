import Hironaka.Resolution.HironakaG1LaterPositiveNormalExample
import Hironaka.Blowup.BlowupFunctionTransform
import Hironaka.Invariant.MemberInterTowerAlong

/-! The selected normal chart at the surviving point after the first blowup. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1LaterPositiveSelectedExample
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1PositiveNormalJointExample HironakaG1PositiveNormalNonspecialExample
  HironakaG1LaterPositiveNormalExample HironakaG1LaterSelectedNormalTangent
  GermIdealOrder ResolutionInvariantSpec StepOneValue StepOneValueMasked BoundaryCount MemberInterLocusAlong HironakaG1RecursiveMemberValueTransport
  RelativePrincipalizationSpan GermIdealPullbackCalculus HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaG8LogClosureHistory HironakaActualCoherentWeightedCoefficientMarked
  InvertibleIdealQuotient IdealWeightPowers RestrictedIdealExtension BlowupControlledTransform
  BlowupFunctionTransform DerivativeIdealAlong TangentDirectionAlong HomogenizedGlueingTower

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev C : Set X := {p}
private abbrev D : Set X := projection U ⁻¹' ((Subtype.val : U → ComplexModel 2) ⁻¹' firstCoordinateDivisor)
private abbrev P : MarkedIdeal 3 X := properNormalMarked sourceRecord
private abbrev A := geoTransformAlong (barMarked P) B
private abbrev V : Opens Y := ⟨yChart.source, yChart.isOpen_source⟩
private abbrev normalOnChart (z : Y) : ℂ := yChart.toFun z (2 : Fin 3)

private theorem p_val : p.val = 0 := map_zero (tangentInclusion 2 1)

private theorem centre_iff (z : Y) (hz : z ∈ V) :
    π z ∈ C ↔ yChart.toFun z (1 : Fin 3) = 0 := by
  constructor
  · intro hp
    have h := congrArg (fun x : X => x.val (1 : Fin 3)) (mem_singleton_iff.mp hp)
    change (π z).val (1 : Fin 3) = p.val (1 : Fin 3) at h
    rw [chart_projection z hz, p_val, monomial_apply] at h
    simpa using h
  · intro ht
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    rw [chart_projection z hz, p_val]
    ext i
    by_cases hi : i = 1
    · subst i
      simpa [monomial_apply] using ht
    · simp [monomial_apply, hi, ht]

/-- In the middle chart, an original coordinate hyperplane other than the
blowup coordinate has strict transform given by its corresponding ratio. -/
theorem strict_chart_coordinate (i : Fin 3) (hi : i ≠ 1) (z : Y) (hz : z ∈ V) :
    z ∈ geoStrictTransform π C {x : X | x.val i = 0} ↔ yChart.toFun z i = 0 := by
  classical
  have hOff (w : Y) (hw : w ∈ V) :
      w ∈ π ⁻¹' ({x : X | x.val i = 0} \ C) ↔
        yChart.toFun w i = 0 ∧ yChart.toFun w (1 : Fin 3) ≠ 0 := by
    rw [mem_preimage, Set.mem_sdiff, centre_iff w hw]
    change (π w).val i = 0 ∧ _ ↔ _
    rw [chart_projection w hw, monomial_apply]
    rw [if_pos (show 0 ≤ i.val ∧ i ≠ (1 : Fin 3) from ⟨Nat.zero_le _, hi⟩), mul_eq_zero]
    tauto
  constructor
  · intro h
    by_contra hz0
    have hCont : ContinuousAt (fun w : Y => yChart.toFun w i) z :=
      (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.continuousAt.comp (yChart.homeo.continuousAt hz)
    have hNear : ∀ᶠ w in 𝓝 z, yChart.toFun w i ≠ 0 :=
      hCont.eventually (isClosed_singleton.isOpen_compl.mem_nhds hz0)
    have hIn := mem_closure_iff_frequently.mp h
    have hV : ∀ᶠ w in 𝓝 z, w ∈ V := V.isOpen.mem_nhds hz
    obtain ⟨w, hw, hwV, hw0⟩ := (hIn.and_eventually (hV.and hNear)).exists
    exact hw0 ((hOff w hwV).mp hw).1
  · intro h
    by_cases ht : yChart.toFun z (1 : Fin 3) = 0
    · let w := yChart.toFun z
      let v : ComplexModel 3 := EuclideanSpace.single (1 : Fin 3) (1 : ℂ)
      let f : ℂ → Y := fun a => yChart.invFun (w + a • v)
      have hF : Tendsto f (𝓝 0) (𝓝 z) := by
        have hC : Continuous (fun a : ℂ => w + a • v) := continuous_const.add (continuous_id.smul continuous_const)
        have h₁ : Tendsto (fun a : ℂ => w + a • v) (𝓝 0) (𝓝 w) := by
          simpa using hC.tendsto (0 : ℂ)
        exact (yChart.homeo.tendsto_symm hz).comp h₁
      have hne : ∃ᶠ a : ℂ in 𝓝 0, a ≠ 0 := by
        have hF' : ∃ᶠ a : ℂ in 𝓝[≠] 0, True :=
          Filter.Eventually.frequently (Filter.Eventually.of_forall fun _ => trivial)
        exact ((frequently_nhdsWithin_iff).mp hF').mono (fun _ ha => ha.2)
      apply mem_closure_iff_frequently.mpr
      exact hF.frequently (hne.mono fun a ha => by
        have hTarget := chart_all (w + a • v)
        have hFsource : f a ∈ V := yChart.toPartialEquiv.map_target hTarget
        have hFcoord : yChart.toFun (f a) = w + a • v := yChart.toPartialEquiv.right_inv hTarget
        apply (hOff (f a) hFsource).mpr
        rw [hFcoord]
        change w i + a * v i = 0 ∧ w (1 : Fin 3) + a * v (1 : Fin 3) ≠ 0
        simp [w, v, hi, h, ht, ha])
    · exact subset_closure ((hOff z hz).mpr ⟨h, ht⟩)

/-- The exceptional function generates the exceptional ideal on the middle chart. -/
theorem equation_on_chart : IsLocalEquation hπ (V : Set Y) exceptionalCoordinate := by
  refine ⟨V.isOpen, ?_, exceptionalCoordinate_nontrivial, ?_⟩
  · intro x hx
    have hV : ∀ᶠ z in 𝓝 x, z ∈ V := V.isOpen.mem_nhds hx
    have hEq : exceptionalCoordinate =ᶠ[𝓝 x] fun z => yChart.toFun z (1 : Fin 3) :=
      hV.mono fun z hz => exceptionalCoordinate_coord z hz
    exact ((yChart.holomorphicAt_coord hx 1).congr hEq.symm).mdifferentiableAt.mdifferentiableWithinAt
  · intro x hx g
    change IsInSpanAt (n := 3) (fun s => ∃ a, (vanishingIdeal (n := 3) C).mem (π x) a ∧ s = a ∘ π) x g ↔ _
    constructor
    · intro hg
      refine IsInSpanAt.of_forall_eq_mul ?_ hg
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, _, hbh, hbeq⟩ := exists_eq_sum_flatCoord yChart.Φ yChart.hsrc yChart.hflat hx.1 ha
      let d := fun (i : Fin 3) (z : Y) => if i = 1 then 1 else yChart.toFun z i
      refine ⟨fun z => ∑ i, b i (π z) * d i z, ?_, ?_⟩
      · refine HolomorphicAt.sum _ fun i _ => (holomorphicAt_comp_blowupProj (hbh i)).mul ?_
        by_cases hi : i = 1
        · simpa [d, hi] using (holomorphicAt_const (n := 3) (x := x) (1 : ℂ))
        · simpa [d, hi] using yChart.holomorphicAt_coord hx i
      · filter_upwards [hπ.contMDiff.continuous.continuousAt.eventually hbeq, V.isOpen.mem_nhds hx] with z hz hzV
        change a (π z) = _
        rw [hz, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hi := yChart.τ_base_eq hzV i
        change yChart.τ i (π z) = monomial 0 (1 : Fin 3) (yChart.toFun z) i at hi
        change b i (π z) * yChart.τ i (π z) = _
        rw [hi, monomial_apply, exceptionalCoordinate_coord z hzV]
        by_cases h : i = 1
        · subst i
          simp [d]
        · simp [d, h, mul_assoc]
    · intro hg
      obtain ⟨hgh, b, hb, heq⟩ := isInSpanAt_eq_iff.mp hg
      exact isInSpanAt_of_eq_mul
        ⟨yChart.τ yChart.j, yChart.τ_mem_vanishingIdeal hx.1 yChart.hj, rfl⟩ hgh hb heq

/-- The literal normal ratio belongs to the order-one controlled transform
on the middle chart of the point blowup. -/
theorem normal_generator (z : Y) (hz : z ∈ V) :
    (controlledTransform hπ P.ideal 1).mem z normalOnChart := by
  let f : X → ℂ := fun x => x.val (2 : Fin 3)
  have hf : P.ideal.mem (π z) f := by
    rw [proper_source_generators]
    have hHol : HolomorphicAt 3 (paddedGenerator (.inr ())) (π z).val :=
      Eventually.of_forall fun w => paddedGenerator_hol (.inr ()) w
    refine GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨paddedGenerator (.inr ()), isInSpanAt_self ⟨.inr (), rfl⟩ hHol, rfl⟩ ?_)
    exact hHol.comp_contMDiff (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)
  refine mem_controlledTransform_of_eq_pow_mul equation_on_chart hz hf
    (yChart.holomorphicAt_coord hz 2) ?_
  filter_upwards [V.isOpen.mem_nhds hz] with w hw
  change (π w).val (2 : Fin 3) = _
  rw [chart_projection w hw, monomial_apply, exceptionalCoordinate_coord w hw, pow_one]
  simp [normalOnChart, mul_comm]

open DerivativeIdeal

private def chart : ComplexChart 3 Y :=
  ⟨yChart.homeo, atlasHomeo_mem_atlas yChart.toPartialEquiv (Or.inl ⟨yChart, rfl⟩)⟩

private def fieldCoeff (i : Fin 3) (_ : Y) : ℂ := if i = 2 then 1 else 0

private theorem field_apply (g : Y → ℂ) (z : Y) :
    fieldDeriv chart fieldCoeff g z =
      chartDeriv chart (EuclideanSpace.single (2 : Fin 3) (1 : ℂ)) g z := by
  simp [fieldDeriv, fieldCoeff]

private theorem normal_field_one (z : Y) (hz : z ∈ V) :
    fieldDeriv chart fieldCoeff normalOnChart z = 1 := by
  rw [field_apply, chartDeriv]
  have hNear : normalOnChart ∘ chart.val.symm =ᶠ[𝓝 (chart.val z)]
      (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)) := by
    filter_upwards [chart.val.open_target.mem_nhds (chart.val.map_source hz)] with w hw
    change yChart.toFun (yChart.invFun w) (2 : Fin 3) = w (2 : Fin 3)
    exact congrArg (fun u : ComplexModel 3 => u (2 : Fin 3)) (yChart.toPartialEquiv.right_inv hw)
  rw [hNear.fderiv_eq, ContinuousLinearMap.fderiv]
  simp

private theorem field_tangent_to_chart_plane (N' : Set Y)
    (hPlane : ∀ w ∈ V, w ∈ N' ↔ yChart.toFun w (0 : Fin 3) = 0)
    (z : Y) (hz : z ∈ V) :
    IsTangentField N' chart fieldCoeff z := by
  have hCoe (i : Fin 3) (w : Y) : HolomorphicAt 3 (fieldCoeff i) w :=
    holomorphicAt_const _
  refine ⟨hz, fun i => hCoe i z, ?_⟩
  intro g hg
  refine ⟨holomorphicAt_fieldDeriv hz (fun i => hCoe i z) hg.1, ?_⟩
  filter_upwards [V.isOpen.mem_nhds hz, hg.1.eventually_nhds, hg.2.eventually_nhds]
    with y hy hyHol hyZero hyN
  have hyCoord := (hPlane y hy).mp hyN
  let w := yChart.toFun y
  let v := EuclideanSpace.single (2 : Fin 3) (1 : ℂ)
  let f : ℂ → ComplexModel 3 := fun a => w + a • v
  have hDiff : DifferentiableAt ℂ (g ∘ chart.val.symm) w :=
    (eventually_differentiableAt_comp_symm chart hy hyHol).self_of_nhds
  have hf : HasDerivAt f v 0 := by
    simpa only [f, id_eq, one_smul] using
      (hasDerivAt_const_add_iff w).mpr ((hasDerivAt_id (0 : ℂ)).smul_const v)
  have hF0 : f 0 = w := by simp [f]
  have hFw : Tendsto f (𝓝 0) (𝓝 w) := by
    rw [← hF0]
    exact hf.continuousAt.tendsto
  have hT : Tendsto (chart.val.symm ∘ f) (𝓝 0) (𝓝 y) :=
    (yChart.homeo.tendsto_symm hy).comp hFw
  have hZero : ((g ∘ chart.val.symm) ∘ f) =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := by
    filter_upwards [hT.eventually hyZero] with a ha
    apply ha
    let y' := chart.val.symm (f a)
    have hTarget := chart_all (f a)
    have hy' : y' ∈ V := yChart.toPartialEquiv.map_target hTarget
    have hCoord : yChart.toFun y' = f a := yChart.toPartialEquiv.right_inv hTarget
    apply (hPlane y' hy').mpr
    rw [hCoord]
    simp [f, w, v, hyCoord]
  have hD : HasDerivAt ((g ∘ chart.val.symm) ∘ f)
      (fderiv ℂ (g ∘ chart.val.symm) w v) 0 :=
    hDiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hf hF0.symm
  have hDZ : HasDerivAt ((g ∘ chart.val.symm) ∘ f) 0 0 :=
    (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hZero
  rw [field_apply]
  exact hD.unique hDZ

open HomogenizedIdealAlong InvDomainMemberRestriction HironakaActualNativeSectionPositiveLowerRecords

private theorem P_dom : IsInvDomain 3 P := properNormalMarked_isInvDomain sourceRecord sourceRecord_domain

private theorem P_bar : barMarked (X := X) P = P := by
  change coeffMarkedAlong (homMarkedAlong P) = P
  rw [homMarkedAlong_eq_of_mark_one P rfl P_dom.isWellFormed.isCoherent,
    coeffMarkedAlong_eq_of_mark_one P rfl P_dom.isWellFormed.isCoherent]

private theorem A_carrier : A.N = univ := by
  change (geoTransformAlong (barMarked (X := X) P) B).N = univ
  rw [P_bar]
  change geoStrictTransform π C P.N = univ
  rw [show P.N = univ from preimage_univ, geoStrictTransform_univ hπ]

private theorem A_mark : A.d = 1 := by
  change (geoTransformAlong (barMarked (X := X) P) B).d = 1
  rw [P_bar]
  rfl

private theorem A_normal_member (z : Y) (hz : z ∈ V) : A.ideal.mem z normalOnChart := by
  change (geoTransformAlong (barMarked (X := X) P) B).ideal.mem z normalOnChart
  rw [P_bar]
  change (P.geoTransform C π).ideal.mem z normalOnChart
  rw [geoTransform_ideal_eq_controlledTransform (𝔪 := P) preimage_univ P_dom.isWellFormed.isCoherent hπ]
  exact normal_generator z hz

private theorem upper_field_tangent (z : Y) (hz : z ∈ V) :
    IsTangentField A.N chart fieldCoeff z := by
  rw [A_carrier]
  refine ⟨hz, fun _ => holomorphicAt_const _, ?_⟩
  intro g hg
  refine ⟨holomorphicAt_fieldDeriv hz (fun _ => holomorphicAt_const _) hg.1, ?_⟩
  have he : g =ᶠ[𝓝 z] fun _ => 0 := hg.2.mono fun _ h => h (mem_univ _)
  have hDer := chartDeriv_congr (e := chart)
    (v := EuclideanSpace.single (2 : Fin 3) (1 : ℂ)) hz he
  exact hDer.mono fun y hy _ => by
    rw [field_apply, hy]
    simp [chartDeriv, Function.comp_def]

private theorem upper_normal_tangent : IsTangentDirectionAlong A.N A.ideal A.d V normalOnChart := by
  rw [A_mark]
  refine ⟨V.isOpen, A_normal_member, ?_⟩
  intro z hz _
  exact ⟨chart, fieldCoeff, upper_field_tangent z hz,
    by rw [normal_field_one z hz]; exact one_ne_zero⟩

private theorem D_eq : D = {x : X | x.val (0 : Fin 3) = 0} := rfl
private theorem zeroPlane_eq : (zeroPlane U : Set X) = {x : X | x.val (2 : Fin 3) = 0} := by
  ext x
  constructor
  · intro hx
    exact congrArg (fun w : ComplexModel 1 => w (0 : Fin 1)) hx.2
  · intro hx
    refine ⟨mem_univ _, ?_⟩
    ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    rw [hi]
    exact hx

private theorem normal_source_eq :
    P.N ∩ {z | HironakaActualRelativeNormalGeometry.relativeNormalCoordinate U z = 0} = zeroPlane U := by
  rw [show P.N = univ from preimage_univ, univ_inter, zeroPlane_eq]
  ext z
  change HironakaActualRelativeNormalGeometry.relativeNormalCoordinate U z = 0 ↔ z.val (2 : Fin 3) = 0
  simp [HironakaActualRelativeNormalGeometry.relativeNormalCoordinate,
    HironakaActualZeroCoordinateContactSeed.addedCoordinate,
    HironakaActualGraphFunctionalIdeal.graphFunction, HironakaActualZeroCoordinateContactSeed.zeroFunction]

private theorem upper_zero :
    A.N ∩ {z | normalOnChart z = 0} ∩ V =
      strictAlong B (P.N ∩ {z | HironakaActualRelativeNormalGeometry.relativeNormalCoordinate U z = 0}) ∩ V := by
  rw [A_carrier, univ_inter, normal_source_eq]
  change {z | normalOnChart z = 0} ∩ V = geoStrictTransform π C (zeroPlane U) ∩ V
  rw [zeroPlane_eq]
  ext z
  constructor
  · rintro ⟨h0, hz⟩
    exact ⟨(strict_chart_coordinate 2 (by decide) z hz).mpr h0, hz⟩
  · rintro ⟨h0, hz⟩
    exact ⟨(strict_chart_coordinate 2 (by decide) z hz).mp h0, hz⟩

private abbrev I := membersThrough A.E (origMembers P B) q
private abbrev K := memberRestrict A I

private theorem orig_eq : origMembers P B = [geoStrictTransform π C D] := by
  rw [origMembers_eq P]
  rfl

private theorem selected_carrier : K.N = geoStrictTransform π C D := by
  have hE : ∀ H ∈ origMembers P B, H ∈ A.E := fun _ h => List.mem_of_mem_take h
  rw [memberRestrict_N, A_carrier, univ_inter, memberInter_membersThrough hE, orig_eq]
  have hqD : q ∈ geoStrictTransform π C D := by
    rw [D_eq]
    exact (strict_chart_coordinate 0 (by decide) q chart_q.1).mpr (by simp [chart_q.2])
  ext z
  simp [hqD]

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
private theorem selected_normal_tangent_on (W : Opens Y) (hWV : W ≤ V) :
    let J := positiveMemberOn P B q W
    IsTangentDirectionAlong J.N J.ideal J.d univ (normalOnChart ∘ (Subtype.val : W → Y)) ∧
      J.N ∩ {z : W | normalOnChart z.val = 0} =
        J.N ∩ (Subtype.val : W → Y) ⁻¹' strictAlong B (zeroPlane U) := by
  intro J
  have hUpper : IsTangentDirectionAlong A.N A.ideal A.d W normalOnChart := by
    exact ⟨W.isOpen, fun z hz => upper_normal_tangent.mem z (hWV hz),
      fun z hz hCos => upper_normal_tangent.multiplicity_one z (hWV hz) hCos⟩
  have hZero : A.N ∩ {z | normalOnChart z = 0} ∩ W =
      strictAlong B (P.N ∩ {z | HironakaActualRelativeNormalGeometry.relativeNormalCoordinate U z = 0}) ∩ W := by
    ext z
    constructor
    · rintro ⟨h, hz⟩
      exact ⟨((Set.ext_iff.mp upper_zero z).mp ⟨h, hWV hz⟩).1, hz⟩
    · rintro ⟨h, hz⟩
      exact ⟨((Set.ext_iff.mp upper_zero z).mpr ⟨h, hWV hz⟩).1, hz⟩
  have hField : ∀ x ∈ W, ∃ (c : ComplexChart 3 Y) (ξ : Fin 3 → Y → ℂ),
      IsTangentField K.N c ξ x ∧
        fieldDeriv c ξ normalOnChart =ᶠ[𝓝 x] fun _ => 1 := by
    intro x hx
    refine ⟨chart, fieldCoeff, ?_, ?_⟩
    · apply field_tangent_to_chart_plane _ _ x (hWV hx)
      intro y hy
      rw [selected_carrier, D_eq]
      exact strict_chart_coordinate 0 (by decide) y hy
    · filter_upwards [V.isOpen.mem_nhds (hWV hx)] with y hy
      exact normal_field_one y hy
  have h := later_positive_member_normal_contact_on_chart sourceRecord sourceRecord_domain B test q W
    normalOnChart hUpper hZero hField
  rw [normal_source_eq] at h
  exact h
set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The literal normal coordinate in the y-chart is a tangent on the actual
later selected carrier. Its selected contact is the strict normal section. -/
theorem joint_first_blowup_selected_normal_tangent :
    let J := positiveMemberOn P B q V
    q ∈ V ∧
    IsTangentDirectionAlong J.N J.ideal J.d univ (normalOnChart ∘ (Subtype.val : V → Y)) ∧
      J.N ∩ {z : V | normalOnChart z.val = 0} =
        J.N ∩ (Subtype.val : V → Y) ⁻¹' strictAlong B (zeroPlane U) := by
  exact ⟨chart_q.1, selected_normal_tangent_on V le_rfl⟩

/-- The survivor at the origin of the middle chart lies in the nonspecial
positive regime. The normal line in the selected member leaves the cosupport. -/
theorem joint_first_blowup_selected_nonspecial : ¬ IsSpecial P B q := by
  intro hSpecial
  rcases hSpecial with hZero | ⟨_, hMember⟩
  · exact (by decide : (1 : ℕ) ≠ 0) (q_level.symm.trans hZero.1)
  let v : ComplexModel 3 := EuclideanSpace.single (2 : Fin 3) (1 : ℂ)
  let f : ℂ → Y := fun a => yChart.invFun (a • v)
  have hT : Tendsto f (𝓝 0) (𝓝 q) := by
    have hf : Continuous (fun a : ℂ => a • v) := continuous_id.smul continuous_const
    have hAt : Tendsto (fun a : ℂ => a • v) (𝓝 0) (𝓝 (yChart.toFun q)) := by
      simpa [chart_q.2] using hf.tendsto (0 : ℂ)
    exact (yChart.homeo.tendsto_symm chart_q.1).comp hAt
  have hne : ∃ᶠ a : ℂ in 𝓝 0, a ≠ 0 := by
    have hF : ∃ᶠ a : ℂ in 𝓝[≠] 0, True :=
      Filter.Eventually.frequently (Filter.Eventually.of_forall fun _ => trivial)
    exact ((frequently_nhdsWithin_iff).mp hF).mono (fun _ ha => ha.2)
  obtain ⟨a, hane, ha⟩ :=
    (hne.and_eventually (hT.eventually (mem_memberInterLocus_iff.mp hMember).2)).exists
  have hTarget := chart_all (a • v)
  have hV : f a ∈ V := yChart.toPartialEquiv.map_target hTarget
  have hCoord : yChart.toFun (f a) = a • v := yChart.toPartialEquiv.right_inv hTarget
  have hD : f a ∈ geoStrictTransform π C D := by
    rw [D_eq]
    exact (strict_chart_coordinate 0 (by decide) _ hV).mpr (by simp [hCoord, v])
  have hCos : f a ∈ A.cosupp := by
    apply ha
    · rw [A_carrier]
      exact mem_univ _
    · intro H hH _
      rw [orig_eq] at hH
      simpa only [List.mem_singleton.mp hH] using hD
  have hN : f a ∈ A.N := hCos.1
  have hOrder := hCos.2 normalOnChart (A_normal_member _ hV)
  rw [A_mark] at hOrder
  have hz := (vanishesToOrderOn_one_iff hN (yChart.holomorphicAt_coord hV 2)).mp hOrder
  exact hane (by simpa [normalOnChart, hCoord, v] using hz)

/-- At the actual length-one survivor the masked Step One value has level one
and a finite lower coordinate. -/
theorem joint_first_blowup_step_one_finite {k : ℕ} {Λ : Type} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0, 0} 3 k Λ) :
    let value := ofLex (Seq.StepOneValueMasked.stepOneInvM R P B q)
    value.1 = 1 ∧ value.2 ≠ ⊤ := by
  have hP := properNormalMarked_isInvDomain sourceRecord sourceRecord_domain
  have hTest : IsGeoTestTower (barMarked (X := X) P) B := by rw [P_bar]; exact test
  have hCos : q ∈ A.cosupp := by
    change q ∈ (geoTransformAlong (barMarked (X := X) P) B).cosupp
    rw [P_bar]
    exact q_cosupp
  have hMax := properNormalMarked_maximalOrder sourceRecord sourceRecord_domain.isWellFormed.isCoherent
  have hNS := joint_first_blowup_selected_nonspecial
  have hFinite := Seq.StepOneValueMasked.lowerValueL_ne_top P R hP.isWellFormed hP.one_le_d
    (by decide) hMax (lowerMarkedM P) B hTest hCos hNS
  refine ⟨(Seq.StepOneValueMasked.stepOneInvL_fst R P (lowerMarkedM P) B q).trans q_level, ?_⟩
  change (ofLex (Seq.StepOneValueMasked.stepOneInvL R P (lowerMarkedM P) B q)).2 ≠ ⊤
  rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R P (lowerMarkedM P) B hNS]
  exact hFinite

/-- The literal normal tangent is available on a neighbourhood of the survivor
inside the actual Step One mask, where its trace is the strict normal section. -/
theorem joint_first_blowup_masked_selected_normal_tangent :
    let W := maskA P B q ⊓ V
    let J := positiveMemberOn P B q W
    q ∈ W ∧
      IsTangentDirectionAlong J.N J.ideal J.d univ (normalOnChart ∘ (Subtype.val : W → Y)) ∧
      J.N ∩ {z : W | normalOnChart z.val = 0} =
        J.N ∩ (Subtype.val : W → Y) ⁻¹' strictAlong B (zeroPlane U) := by
  have hTest : IsGeoTestTower (barMarked (X := X) P) B := by rw [P_bar]; exact test
  have hMask := StepOneLowerDomain.mem_maskA P P_dom.isWellFormed P_dom.one_le_d
    (by decide) B hTest (y₀ := q) (by rw [q_level]) joint_first_blowup_selected_nonspecial
  exact ⟨⟨hMask, chart_q.1⟩, selected_normal_tangent_on _ inf_le_right⟩

end
end Hironaka.HironakaG1LaterPositiveSelectedExample
