import Hironaka.Resolution.HironakaG1PositiveNormalJointExample
import Hironaka.Resolution.HironakaActualAnchoredStrictCarrierMask
import Hironaka.Resolution.HironakaG1LaterSelectedNormalTangent

/-! An actual first nonempty blowup in the joint coordinate example. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1LaterPositiveNormalExample
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1PositiveNormalJointExample HironakaG1PositiveNormalNonspecialExample
  HironakaOneDimensionalCanonicalSuperlevels BlowupExistenceOriginIdeal
  GermIdealOrder ResolutionInvariantSpec StepOneValue BoundaryCount
  RelativePrincipalizationSpan

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev C : Set X := {p}
private abbrev D : Set X := projection U ⁻¹' ((Subtype.val : U → ComplexModel 2) ⁻¹' firstCoordinateDivisor)
private abbrev P : MarkedIdeal 3 X := properNormalMarked sourceRecord
private theorem p_val : p.val = 0 := map_zero (tangentInclusion 2 1)
private theorem product_top : productOpen U = ⊤ := by
  apply Opens.ext
  change tangentProjection 2 1 ⁻¹' (univ : Set (ComplexModel 2)) = univ
  exact preimage_univ
private theorem preimage_point : (Subtype.val : X → ComplexModel 3) ⁻¹' ({0} : Set (ComplexModel 3)) = C := by
  ext x
  exact ⟨fun hx => Subtype.ext (hx.trans p_val.symm), fun hx => (congrArg Subtype.val hx).trans p_val⟩
private theorem centre_smooth : IsClosedSubmanifold 3 C :=
  (PointSupportedIdealPrincipalization.singleton_geometry_and_coherence (n := 3) p).1
private theorem centre_thin : interior C = ∅ := by
  have hf : IsOpenMap (Subtype.val : X → ComplexModel 3) := (productOpen U).isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  rw [← preimage_point, ← hf.preimage_interior_eq_interior_preimage continuous_subtype_val,
    interior_zero_eq_empty (by decide : 0 < 3), preimage_empty]
private instance : Fact (IsClosedSubmanifold 3 C) := ⟨centre_smooth⟩
/-- The actual ambient manifold after blowing up the common origin. -/
abbrev Y := CMfd.of (n := 3) (BlowupSpace 3 C)
/-- The projection of the actual point blowup. -/
abbrev π : Y → X := blowupProj 3 C
/-- The universal blowup property of the concrete point projection. -/
theorem hπ : IsBlowupAlong 3 C π := isBlowupAlong_blowupProj centre_thin

private theorem chart_apply (x : X) : chartAt (ComplexModel 3) p x = x.val := by
  rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
  rfl

/-- The literal middle-coordinate chart of the concrete point blowup. -/
def yChart : FlatChart 3 C where
  y₀ := p
  k := 0
  Φ :=
    { source := univ
      target := univ
      isOpen_source := isOpen_univ
      isOpen_target := isOpen_univ
      center_mem_source := mem_univ _
      toFun := id
      invFun := id
      toFun_holomorphic := differentiable_id.differentiableOn
      invFun_holomorphic := differentiable_id.differentiableOn
      mapsTo_toFun := mapsTo_univ _ _
      mapsTo_invFun := mapsTo_univ _ _
      left_inv := fun _ _ => rfl
      right_inv := fun _ _ => rfl }
  hsrc := by
    rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
    intro w _
    let x : productOpen U := ⟨w, by rw [product_top]; exact mem_univ _⟩
    exact (OpenPartialHomeomorph.refl (ComplexModel 3)).map_subtype_source
      ⟨x⟩ (x := x) (mem_univ _)
  hflat := by
    intro x _ _
    have h : x ∈ C ↔ x.val = 0 := by
      exact ⟨fun hx => (congrArg Subtype.val hx).trans p_val, fun hx => Subtype.ext (hx.trans p_val.symm)⟩
    rw [h, ← zero_eq_complexCoordinatePlane]
    change x.val = 0 ↔ chartAt (ComplexModel 3) p x = 0
    rw [chart_apply]
  j := 1
  hj := Nat.zero_le _

/-- The middle-coordinate chart has the whole model space as target. -/
theorem chart_all (w : ComplexModel 3) : w ∈ yChart.target := by
  change monomial 0 (1 : Fin 3) w ∈ univ
  exact mem_univ _
/-- The point with all chart coordinates zero over the common centre. -/
abbrev q : Y := yChart.invFun 0

/-- The surviving point is the origin in the actual middle-coordinate chart. -/
theorem chart_q : q ∈ yChart.source ∧ yChart.toFun q = 0 :=
  ⟨yChart.toPartialEquiv.map_target (chart_all 0), yChart.toPartialEquiv.right_inv (chart_all 0)⟩

/-- The exact blowdown formula in the actual middle-coordinate chart. -/
theorem chart_projection (z : Y) (hz : z ∈ yChart.source) :
    (π z).val = monomial 0 (1 : Fin 3) (yChart.toFun z) := by
  have h := (yChart.monomial_toFun hz).symm
  change chartAt (ComplexModel 3) p (π z) = _ at h
  rw [chart_apply] at h
  exact h

private theorem q_proj : π q = p := by
  apply Subtype.ext
  rw [chart_projection q chart_q.1, chart_q.2, p_val]
  ext i
  simp [monomial_apply]
private def γ (a : ℂ) : Y := yChart.invFun (a • EuclideanSpace.single (1 : Fin 3) (1 : ℂ))

private theorem γ_tendsto : Tendsto γ (𝓝 0) (𝓝 q) := by
  have h : Tendsto (fun a : ℂ => a • EuclideanSpace.single (1 : Fin 3) (1 : ℂ))
      (𝓝 0) (𝓝 (0 : ComplexModel 3)) := by
    have hC : Continuous (fun a : ℂ => a • EuclideanSpace.single (1 : Fin 3) (1 : ℂ)) :=
      continuous_id.smul continuous_const
    simpa using hC.tendsto (0 : ℂ)
  have hi := yChart.homeo.tendsto_symm (x := q) chart_q.1
  change Tendsto yChart.invFun (𝓝 (yChart.toFun q)) (𝓝 q) at hi
  rw [chart_q.2] at hi
  exact hi.comp h

private theorem γ_proj (a : ℂ) : (π (γ a)).val = a • EuclideanSpace.single (1 : Fin 3) (1 : ℂ) := by
  let w : ComplexModel 3 := a • EuclideanSpace.single (1 : Fin 3) (1 : ℂ)
  have hz : γ a ∈ yChart.source := yChart.toPartialEquiv.map_target (chart_all w)
  have hzinv : yChart.toFun (γ a) = w := yChart.toPartialEquiv.right_inv (chart_all w)
  rw [chart_projection _ hz, hzinv]
  ext i
  by_cases hi : i = 1
  · subst i
    rw [monomial_apply]
    simp [w]
  · rw [monomial_apply]
    simp [hi, w]

private theorem q_strict_of_axis (A : Set X)
    (hAxis : ∀ a : ℂ, a ≠ 0 → π (γ a) ∈ A) : q ∈ geoStrictTransform π C A := by
  apply mem_closure_iff_frequently.mpr
  have hne : ∃ᶠ a : ℂ in 𝓝 0, a ≠ 0 := by
    have hF : ∃ᶠ a : ℂ in 𝓝[≠] 0, True := Filter.Eventually.frequently (Filter.Eventually.of_forall fun _ => trivial)
    exact ((frequently_nhdsWithin_iff).mp hF).mono (fun _ ha => ha.2)
  exact γ_tendsto.frequently (hne.mono fun a ha => by
    refine ⟨hAxis a ha, ?_⟩
    intro hc
    have hp := congrArg (fun x : X => x.val (1 : Fin 3)) (mem_singleton_iff.mp hc)
    change (π (γ a)).val (1 : Fin 3) = p.val (1 : Fin 3) at hp
    rw [γ_proj a, p_val] at hp
    exact ha (by simpa using hp))

private theorem q_strict_D : q ∈ geoStrictTransform π C D := by
  apply q_strict_of_axis
  intro a _
  change tangentProjection 2 1 (π (γ a)).val (0 : Fin 2) = 0
  rw [γ_proj a, tangentProjection_apply]
  change (a • EuclideanSpace.single (1 : Fin 3) (1 : ℂ)) (0 : Fin 3) = 0
  simp

private theorem q_strict_section : q ∈ geoStrictTransform π C (zeroPlane U) := by
  apply q_strict_of_axis
  intro a _
  refine ⟨mem_univ _, ?_⟩
  rw [γ_proj a]
  ext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  rw [hi]
  change (a • EuclideanSpace.single (1 : Fin 3) (1 : ℂ)) (2 : Fin 3) = 0
  simp

open GermIdealPullbackCalculus HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaG8LogClosureHistory HironakaActualCoherentWeightedCoefficientMarked
  InvertibleIdealQuotient IdealWeightPowers RestrictedIdealExtension BlowupControlledTransform

private theorem P_dom : IsInvDomain 3 P := properNormalMarked_isInvDomain sourceRecord sourceRecord_domain

/-- The pullback of the middle coordinate appearing in the exceptional equation. -/
abbrev exceptionalCoordinate : Y → ℂ := yChart.τ yChart.j ∘ π

/-- The exceptional function is the middle chart coordinate. -/
theorem exceptionalCoordinate_coord (z : Y) (hz : z ∈ yChart.source) :
    exceptionalCoordinate z = yChart.toFun z (1 : Fin 3) := by
  exact (yChart.τ_base_eq hz yChart.j).trans (yChart.monomial_apply_j _)

/-- The exceptional function vanishes identically on no nonempty open in the chart. -/
theorem exceptionalCoordinate_nontrivial :
    ∀ V : Set Y, IsOpen V → V ⊆ yChart.source → V.Nonempty → ∃ z ∈ V, exceptionalCoordinate z ≠ 0 := by
  rintro V hV hSub ⟨z, hz⟩
  have hN := yChart.homeo.image_mem_nhds (hSub hz) (hV.mem_nhds hz)
  obtain ⟨u, ⟨w, hw, rfl⟩, hu⟩ := exists_coord_ne_zero_of_mem_nhds hN (1 : Fin 3)
  exact ⟨w, hw, by rwa [exceptionalCoordinate_coord w (hSub hw)]⟩

private def quotientGen (j : Bool ⊕ Unit) (z : Y) : ℂ :=
  match j with
  | .inl false => yChart.toFun z (1 : Fin 3)
  | .inl true => yChart.toFun z (0 : Fin 3)
  | .inr _ => yChart.toFun z (2 : Fin 3)

private theorem quotientGen_hol (j : Bool ⊕ Unit) : HolomorphicAt 3 (quotientGen j) q := by
  rcases j with (_ | _) | _
  · exact yChart.holomorphicAt_coord chart_q.1 1
  · exact yChart.holomorphicAt_coord chart_q.1 0
  · exact yChart.holomorphicAt_coord chart_q.1 2

private theorem quotientGen_zero (j : Bool ⊕ Unit) : quotientGen j q = 0 := by
  rcases j with (_ | _) | _
  all_goals simp only [quotientGen, chart_q.2, WithLp.ofLp_zero, Pi.zero_apply]

private theorem generator_divides (j : Bool ⊕ Unit) :
    (fun z : Y => paddedGenerator j (π z).val) =ᶠ[𝓝 q] fun z => exceptionalCoordinate z * quotientGen j z := by
  filter_upwards [yChart.isOpen_source.mem_nhds chart_q.1] with z hz
  rw [chart_projection z hz, exceptionalCoordinate_coord z hz]
  rcases j with (_ | _) | _
  · change monomial 0 (1 : Fin 3) (yChart.toFun z) (1 : Fin 3) ^ 2 = _
    rw [monomial_apply]
    simp [quotientGen, pow_two]
  · change monomial 0 (1 : Fin 3) (yChart.toFun z) (0 : Fin 3) = _
    rw [monomial_apply]
    simp [quotientGen, mul_comm]
  · change monomial 0 (1 : Fin 3) (yChart.toFun z) (2 : Fin 3) = _
    rw [monomial_apply]
    simp [quotientGen, mul_comm]

private theorem controlled_vanish (g : Y → ℂ)
    (hg : (controlledTransform hπ P.ideal 1).mem q g) : g q = 0 := by
  let i : X → ComplexModel 3 := Subtype.val
  let f : Y → ComplexModel 3 := i ∘ π
  have hi : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) ∞ i := contMDiff_subtype_val
  have hf : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) ∞ f := hi.comp hπ.contMDiff
  have hCoh : paddedCoordinateIdeal.IsCoherent :=
    isCoherent_finiteFunctionIdeal paddedGenerator paddedGenerator_hol
  have hLambda : (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal.mem q exceptionalCoordinate := by
    change (GermIdeal.pullback (m := 3) π (vanishingIdeal (n := 3) C)).mem q (yChart.τ yChart.j ∘ π)
    exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self
      ⟨yChart.τ yChart.j, yChart.τ_mem_vanishingIdeal chart_q.1.1 yChart.hj, rfl⟩
      (holomorphicAt_comp_blowupProj (yChart.holomorphicAt_τ yChart.j chart_q.1.1)))
  have hLambda1 : (idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal 1).mem q exceptionalCoordinate := by
    rw [BlowupStrictIdeal.idealPow_one_exceptionalDivisor hπ]
    exact hLambda
  have hPB := (mem_colon_iff.mp hg).2 _ hLambda1
  rw [proper_source_generators, ← coherent_pullback_comp hi hπ.contMDiff _ hCoh] at hPB
  have hSpan : IsInSpanAt (n := 3) (fun b => ∃ j, b = paddedGenerator j ∘ f) q (exceptionalCoordinate * g) := by
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hPB)
    rintro _ ⟨u, hu, rfl⟩
    refine (isInSpanAt_comp' hf hu).mono ?_
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩
  obtain ⟨_, k, s, b, hs, hb, he⟩ := hSpan
  choose j hj using hs
  let G : Y → ℂ := fun z => ∑ l, b l z * quotientGen (j l) z
  have hG : HolomorphicAt 3 G q := HolomorphicAt.sum _ fun l _ => (hb l).mul (quotientGen_hol (j l))
  have hCancel : ∀ᶠ z in 𝓝 q, exceptionalCoordinate z * g z = exceptionalCoordinate z * G z := by
    filter_upwards [he, eventually_all.mpr (fun l => generator_divides (j l))] with z hz hzDiv
    change exceptionalCoordinate z * g z = ∑ l, b l z * s l z at hz
    rw [hz, show G z = ∑ l, b l z * quotientGen (j l) z from rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hj l]
    change b l z * paddedGenerator (j l) (π z).val = _
    rw [hzDiv l]
    ring
  have hEq := eventuallyEq_of_mul_eventuallyEq yChart.isOpen_source exceptionalCoordinate_nontrivial chart_q.1
    (mem_colon_iff.mp hg).1 hG hCancel
  rw [hEq.self_of_nhds]
  simp [G, quotientGen_zero]

open HomogenizedGlueingTower HironakaG8HomStable HironakaG8LocalHistory
  HironakaG1ProperCarrierNormalLocalClass HironakaG1LaterSelectedNormalTangent

private theorem centre_admissible : P.IsAdmissibleCentre C := by
  obtain ⟨_, _, _, _, _, _, _, _, hp, _, _, _, _, _, _, _, _⟩ :=
    joint_positive_nonspecial_first_entries
  exact ⟨centre_smooth, singleton_subset_iff.mpr hp,
    hasNormalCrossings_singleton p P_dom.isWellFormed.isSNCDivisor⟩

/-- The one-step tower that blows up the common origin. -/
abbrev B : BlowupTower X Y := .step .refl C π hπ
/-- The concrete one-step tower is an actual padded test tower. -/
theorem test : IsGeoTestTower P B := ⟨trivial, centre_admissible⟩

/-- The middle-chart origin survives in the transformed padded cosupport. -/
theorem q_cosupp : q ∈ (geoTransformAlong P B).cosupp := by
  change q ∈ (P.geoTransform C π).cosupp
  have hPN : P.N = univ := preimage_univ
  have hN : (P.geoTransform C π).N = univ := by
    change geoStrictTransform π C P.N = univ
    rw [hPN, geoStrictTransform_univ hπ]
  have hI := geoTransform_ideal_eq_controlledTransform (𝔪 := P) hPN P_dom.isWellFormed.isCoherent hπ
  have hMark : (P.geoTransform C π).d = 1 := rfl
  change q ∈ cosupport 3 (P.geoTransform C π).N (P.geoTransform C π).ideal (P.geoTransform C π).d
  rw [hN, hI, hMark]
  refine ⟨mem_univ _, fun g hg => ?_⟩
  exact (vanishesToOrderOn_one_iff (mem_univ q) (mem_colon_iff.mp hg).1).mpr
    (controlled_vanish g hg)

/-- The surviving point has one original boundary member. -/
theorem q_level : level P B q = 1 := by
  have he : origMembers P B = [geoStrictTransform π C D] := by
    rw [origMembers_eq P]
    rfl
  unfold level
  rw [he]
  classical
  unfold boundaryCount
  rw [Finset.filter_true_of_mem]
  · simp
  · intro i _
    have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
    simpa [List.get_eq_getElem, hi] using q_strict_D

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The first actual blowup of the common origin has a surviving cosupport
point on the strict original boundary and strict section in the y-chart.
Its original level is one, and the later upper bar has a normal contact there. -/
theorem joint_first_point_blowup_positive_normal_contact :
    IsGeoTestTower P B ∧ IsGeoTestTower (sectionMarked sourceRecord) B ∧
      B.length = 1 ∧ π q = p ∧
      q ∈ (geoTransformAlong P B).cosupp ∧
      q ∈ geoStrictTransform π C D ∧ q ∈ geoStrictTransform π C (zeroPlane U) ∧
      level P B q = 1 ∧
      let A := geoTransformAlong (barMarked P) B
      ∃ (V : Opens Y) (u : Y → ℂ), q ∈ V ∧
        TangentDirectionAlong.IsTangentDirectionAlong A.N A.ideal A.d V u ∧
        A.N ∩ {z | u z = 0} ∩ V =
          strictAlong B (P.N ∩ {z | HironakaActualRelativeNormalGeometry.relativeNormalCoordinate U z = 0}) ∩ V := by
  have hsec := ((properNormalMarked_locWPEquiv_section sourceRecord sourceRecord_domain).wEquiv.2 B).1.mp test
  have hBar := ((bar_local_any_boundary (X := X) P P_dom).wEquiv.2 B).2 test
  have hqBar : q ∈ (geoTransformAlong (barMarked P) B).cosupp := hBar ▸ q_cosupp
  exact ⟨test, hsec, rfl, q_proj, q_cosupp, q_strict_D, q_strict_section, q_level,
    later_normal_bar_contact sourceRecord sourceRecord_domain B test
      ((geoTransformAlong (barMarked P) B).cosupp_subset_N hqBar)⟩

end
end Hironaka.HironakaG1LaterPositiveNormalExample
