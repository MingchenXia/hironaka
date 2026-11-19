import Hironaka.Resolution.HironakaG8OddCuspGeometricSource
import Hironaka.Resolution.HironakaG8ChronologicalRestartObstruction
import Hironaka.Resolution.HironakaActualControlledNeighborhoodGenerators
import Hironaka.Blowup.BlowupExistenceOriginUniversal
import Hironaka.Resolution.HironakaG8LogFiniteSumTransform

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8ReducedCuspControlledObstruction
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HolGerm MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  RelativePrincipalizationSpan HironakaRelativeNormalAnalyticGraphQuotient
  HironakaRelativeNormalIdeal HironakaG8SameHSCuspContact HironakaG8NativeCuspDiagram
  HironakaRelativeNormalDeformationInitialRelations HironakaActualControlledNeighborhoodGenerators
  HironakaG8OddCuspVanishingStalk HironakaG8OddCuspGeometricSource
  BlowupExistenceOriginModel BlowupExistenceOriginGenerator BlowupExistenceOriginUniversal
  BlowupExistenceOriginIdeal BlowupStrictIdeal BlowupExceptionalDivisor BlowupControlledTransform
  InvertibleIdealQuotient GermIdealOrder GermIdealPullbackCalculus
  BlowupTowers OkaIdealOperations HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetChartInvariance CompanionReduction NormalCrossings
  HironakaEmbeddedAnalytic BlowupStrictSubmanifold GermIdealTotalTransform
  DivisorExponentAlong NonmonomialOrderLocal MonomialPartAlong IdealWeightPowers
  RestrictedIdealExtension HironakaG11PresLineState HironakaG8LocalHistory CanonicalCentres
private theorem equations_differentiable (p : ℕ) (i : Fin 2) :
    Differentiable ℂ (embeddedCuspEquations p i) := by
  by_cases hi : i = 0
  · rw [show embeddedCuspEquations p i =
      fun z => z.ofLp 1 ^ 2 - z.ofLp 0 ^ p by funext z; exact if_pos hi]
    exact ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).differentiable.pow 2).sub
      ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).differentiable.pow p)
  · rw [show embeddedCuspEquations p i =
      fun z => z.ofLp 2 by funext z; exact if_neg hi]
    exact (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiable

private def equationGerm (p : ℕ) (i : Fin 2) : HolGerm (ComplexModel 3) :=
  HolGerm.mk (embeddedCuspEquations p i) (Eventually.of_forall (equations_differentiable p i))

private theorem first_equation_germ (p : ℕ) :
    equationGerm p 0 = tangentPullback 2 1 (cuspGerm p) := by
  change equationGerm p 0 = tangentPullback 2 1
    ((normalCoordinate 1 1 0)^2 - (tangentPullback 1 1 (normalCoordinate 0 1 0))^p)
  rw [map_sub, map_pow, map_pow]
  unfold tangentPullback normalCoordinate coordinateGerm
  rw [compAlgHom_mk, compAlgHom_mk, compAlgHom_mk, ← mk_pow, ← mk_pow, ← mk_sub]
  exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun _ => rfl)

private theorem second_equation_germ (p : ℕ) :
    equationGerm p 1 = normalCoordinate 2 1 0 := by
  unfold equationGerm normalCoordinate coordinateGerm
  exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun _ => rfl)

private theorem equation_span (p : ℕ) :
    Ideal.span (range (equationGerm p)) = embeddedCuspIdeal p := by
  have hRange : range (equationGerm p) = {tangentPullback 2 1 (cuspGerm p), normalCoordinate 2 1 0} := by
    ext g
    simp only [mem_range, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl (first_equation_germ p)
      · exact Or.inr (second_equation_germ p)
    · rintro (rfl | rfl)
      · exact ⟨0, first_equation_germ p⟩
      · exact ⟨1, second_equation_germ p⟩
  have hNormal : range (normalCoordinate 2 1) = {normalCoordinate 2 1 0} := by
    ext g
    simp only [mem_range, mem_singleton_iff]
    constructor
    · rintro ⟨a,rfl⟩
      rw [Subsingleton.elim a 0]
    · rintro rfl
      exact ⟨0,rfl⟩
  rw [hRange, embeddedCuspIdeal, HironakaActualZeroSectionStabilization.actualZeroSectionIdeal,
    Ideal.map_span, Set.image_singleton, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    normalIdeal, hNormal, ← Ideal.span_union]
  congr 1


private abbrev A := vanishingIdeal (n := 3) (embeddedCuspSet 5)
private theorem hA : A.IsCoherent :=
  CartanIrreducible.cartanCoherence _ (embedded_cusp_isAnalytic 5)

private theorem span_iff {N : ℕ} (s : Fin N → ComplexModel 3 → ℂ)
    (x : ComplexModel 3) (f : ComplexModel 3 → ℂ) :
    IsInSpanAt (n := 3) (· ∈ range s) x f ↔ InSpanAt s x f := by
  rw [CoherentIdealColon.isInSpanAt_range_iff]
  constructor
  · rintro ⟨hf,a,ha,he⟩
    exact ⟨hf.mono (fun _ h => h.differentiableAt),a,fun i => (ha i).mono (fun _ h => h.differentiableAt),he⟩
  · rintro ⟨hf,a,ha,he⟩
    exact ⟨hf.mono (fun _ h => h.mdifferentiableAt),a,fun i => (ha i).mono (fun _ h => h.mdifferentiableAt),he⟩

/-- The actual equations generate the coherent reduced ideal on a common
source neighborhood of the centre. -/
theorem reduced_cusp_source_generators :
    ∃ U : Set (ComplexModel 3), IsOpen U ∧ 0 ∈ U ∧
      ∀ x ∈ U, ∀ g, A.mem x g ↔ InSpanAt (embeddedCuspEquations 5) x g := by
  obtain ⟨V,hV,h0,k,s,hs,hgen⟩ := hA 0
  have hFG : IdealFGAt A.mem (0 : ComplexModel 3) :=
    ⟨V,hV,h0,Fin k,inferInstance,s,
      fun i x hx => ((hs i x hx).mdifferentiableAt (hV.mem_nhds hx)).differentiableAt.differentiableWithinAt,
      fun x hx f => (hgen x hx f).trans (span_iff s x f)⟩
  obtain ⟨U,hU,h0U,_,hgenU⟩ := exists_actual_neighborhood_of_same_origin_generators
    A hFG (embeddedCuspEquations 5) (fun i => Eventually.of_forall (equations_differentiable 5 i))
    ((equation_span 5).trans (embedded_odd_cusp_vanishing_stalk 5 (by decide)).symm)
  exact ⟨U,hU,h0U,hgenU⟩

private abbrev Y := CMfd.of (n := 3) (OriginBlowup 3)
private abbrev X := CMfd.of (n := 3) (ComplexModel 3)
private abbrev cuspMarkOne : MarkedIdeal 3 X := ⟨univ,[],A,1⟩
private abbrev B : MarkedIdeal 3 Y :=
  cuspMarkOne.geoTransform ({0} : Set X) originProj
private abbrev y : Y := originMk 0 (PiLp.single 2 (1 : Fin 3) (1 : ℂ))
private abbrev u : Y → ℂ := originGen 0
private abbrev v : Y → ℂ := fun z => originCoord 0 z 1
private abbrev w : Y → ℂ := fun z => originCoord 0 z 2
private def q (i : Fin 2) : Y → ℂ := if i = 0 then fun z => u z * (v z ^ 2 - u z ^ 3) else w
private abbrev hπ := isBlowupAlong_originProj (d:=3) (by decide)

private theorem hyU : y ∈ originSource 0 := originMk_mem_originSource 0 _
private theorem hyP : originProj y = 0 := by
  change (_ • gen (0 : Fin 3) _ : ComplexModel 3) = 0
  simp
private theorem hyu : u y = 0 := by simp
private theorem hyw : w y = 0 := by simp [w,y,originCoord_originMk,show (2 : Fin 3) ≠ 1 by decide]

private theorem hqHol (i : Fin 2) : HolomorphicAt 3 (q i) y := by
  have hu := holomorphicAt_originGen hyU
  have hv : HolomorphicAt 3 v y :=
    holomorphicAt_comp_originCoord ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).differentiable) hyU
  have hw : HolomorphicAt 3 w y :=
    holomorphicAt_comp_originCoord ((EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiable) hyU
  fin_cases i
  · change HolomorphicAt 3 (fun z => u z * (v z ^ 2 - u z ^ 3)) y
    filter_upwards [hu,hv] with z huz hvz
    exact huz.mul ((hvz.pow 2).sub (huz.pow 3))
  · exact hw

private theorem total_equation_factor (z : Y) (hz : z ∈ originSource 0) (i : Fin 2) :
    embeddedCuspEquations 5 i (originProj z) = u z * q i z := by
  have h0 : originProj z 0 = u z := by
    rw [originProj_apply_eq hz 0]
    simp [gen]
  have h1 : originProj z 1 = u z * v z := by
    rw [originProj_apply_eq hz 1]
    simp [gen,v,show (1 : Fin 3) ≠ 0 by decide]
  have h2 : originProj z 2 = u z * w z := by
    rw [originProj_apply_eq hz 2]
    simp [gen,w,show (2 : Fin 3) ≠ 0 by decide]
  fin_cases i
  · change originProj z 1 ^ 2 - originProj z 0 ^ 5 = u z * (u z * (v z ^ 2 - u z ^ 3))
    rw [h0,h1]
    ring
  · exact h2

private theorem total_at_competitor_isInSpan {g : Y → ℂ}
    (hg : (GermIdeal.pullback (m := 3) originProj A).mem y g) :
    IsInSpanAt (n := 3) (· ∈ range (fun i => embeddedCuspEquations 5 i ∘ originProj)) y g := by
  obtain ⟨U,_,h0,hgen⟩ := reduced_cusp_source_generators
  have hG := GermIdeal.mem_pullback_iff.mp hg
  refine IsInSpanAt.trans ?_ hG
  rintro _ ⟨f,hf,rfl⟩
  have hF : IsInSpanAt (n := 3) (· ∈ range (embeddedCuspEquations 5)) (originProj y) f := by
    rw [hyP] at hf ⊢
    exact (span_iff _ _ _).mpr ((hgen 0 h0 f).mp hf)
  apply IsInSpanAt.mono _ (HironakaG8LogFiniteSumTransform.isInSpanAt_comp hπ.contMDiff hF)
  rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
  exact ⟨i,rfl⟩

/-- The controlled transform of the reduced mark-one cusp is active at
the exceptional direction `(1:1:0)`. -/
theorem reduced_cusp_exceptional_competitor_active : y ∈ B.cosupp := by
  have hBN : B.N = univ := geoTransform_N_eq_univ rfl hπ
  change y ∈ cosupport 3 B.N B.ideal B.d
  rw [hBN]
  refine ⟨mem_univ y,fun f hf => ?_⟩
  have hf' : (colon (GermIdeal.pullback (m := 3) originProj A) (exceptionalDivisor hπ).ideal).mem y f := by
    rwa [show B.ideal = controlledTransform hπ A 1 from geoTransform_ideal_eq_controlledTransform rfl hA hπ,
      controlledTransform,idealPow_one_exceptionalDivisor] at hf
  obtain ⟨hfHol,hMul⟩ := mem_colon_iff.mp hf'
  have hExc : (exceptionalDivisor hπ).ideal.mem y (fun z => originProj z 0) :=
    compFun_mem_pullback hπ.contMDiff (0 : Fin 3) y
  obtain ⟨_,N,s,c,hs,hc,hsum⟩ := total_at_competitor_isInSpan (hMul _ hExc)
  choose j hj using hs
  have hSumHol : HolomorphicAt 3 (fun z => ∑ i, c i z * q (j i) z) y :=
    HolomorphicAt.sum _ fun i _ => (hc i).mul (hqHol (j i))
  have hEq : f =ᶠ[𝓝 y] fun z => ∑ i, c i z * q (j i) z := by
    apply eventuallyEq_of_mul_eventuallyEq (isOpen_originSource 0)
      (fun _ hW hSub hNe => exists_originGen_ne_zero hW hSub hNe) hyU hfHol hSumHol
    filter_upwards [hsum,(isOpen_originSource 0).mem_nhds hyU] with z hz hzU
    have h0 : originProj z 0 = u z := by
      rw [originProj_apply_eq hzU 0]
      simp [gen]
    change originProj z 0 * f z = ∑ i, c i z * s i z at hz
    rw [h0] at hz
    change u z * f z = u z * ∑ i, c i z * q (j i) z
    rw [hz,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hj i]
    change c i z * embeddedCuspEquations 5 (j i) (originProj z) = _
    rw [total_equation_factor z hzU]
    ring
  have hZero : f y = 0 := by
    rw [hEq.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _
    have hj0 : q (j i) y = 0 := by
      unfold q
      split
      · change u y * (v y ^ 2 - u y ^ 3) = 0
        rw [hyu,zero_mul]
      · exact hyw
    simp [hj0]
  change VanishesToOrderOn 3 univ y 1 f
  exact (vanishesToOrderOn_one_iff (mem_univ y) hfHol).mpr hZero

/-- The occupied point blowup is a legitimate singular-centred TEST of
the original reduced mark-one record. -/
theorem reduced_cusp_origin_step_isGeoTestTower :
    IsGeoTestTower cuspMarkOne (BlowupTower.step (Z := Y) .refl ({0} : Set X) originProj hπ) := by
  have hs := embedded_odd_cusp_singular_at_zero 5 (by decide) (by decide)
  have h0 : (0 : X) ∈ embeddedCuspSet 5 := singularSet_subset _ hs
  have hCos : (0 : X) ∈ cuspMarkOne.cosupp := by
    change (0 : X) ∈ cosupport 3 univ A 1
    refine ⟨mem_univ _,fun f hf => ?_⟩
    apply (vanishesToOrderOn_one_iff (mem_univ (0 : X))
      (GermIdeal.IsCoherent.holomorphicAt_mem hA hf)).mpr
    exact hf.2.self_of_nhds h0
  exact ⟨trivial,hπ.1,fun x hx => (mem_singleton_iff.mp hx).symm ▸ hCos,
    hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1⟩

private theorem reduced_cusp_competitor_off_geoStrict :
    y ∉ geoStrictTransform originProj ({0} : Set X) (embeddedCuspSet 5) := by
  let H : ComplexModel 3 → ℂ := fun z => z 1 ^ 2 - z 0 ^ 3
  have hCont (i : Fin 3) : Continuous (fun z : ComplexModel 3 => z i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).continuous
  have hHCont : Continuous H := ((hCont 1).pow 2).sub ((hCont 0).pow 3)
  let N : Set Y := originSource 0 ∩ originCoord 0 ⁻¹' (H ⁻¹' ({0} : Set ℂ)ᶜ)
  have hN : IsOpen N := (continuousOn_originCoord 0).isOpen_inter_preimage
    (isOpen_originSource 0) (hHCont.isOpen_preimage _ (isClosed_singleton.isOpen_compl))
  have hyN : y ∈ N := ⟨hyU,by
    change H (originCoord 0 y) ∉ ({0} : Set ℂ)
    rw [show originCoord 0 y = _ from originCoord_originMk 0 _]
    simp [H]⟩
  intro hNear
  obtain ⟨r,hrN,hrA⟩ := mem_closure_iff.mp hNear N hN hyN
  have huNe : u r ≠ 0 := by
    intro hz
    exact hrA.2 (mem_singleton_iff.mpr ((originProj_eq_zero_iff hrN.1).mpr hz))
  have hEq := total_equation_factor r hrN.1 (0 : Fin 2)
  have hZero : embeddedCuspEquations 5 0 (originProj r) = 0 := hrA.1 0
  rw [hZero] at hEq
  have hq0 : q 0 r = 0 := (mul_eq_zero.mp hEq.symm).resolve_left huNe
  have hH : H (originCoord 0 r) = 0 := by
    change v r ^ 2 - (originCoord 0 r 0) ^ 3 = 0
    rw [show originCoord 0 r 0 = u r from rfl]
    apply (mul_eq_zero.mp ?_).resolve_left huNe
    exact hq0
  exact hrN.2 (mem_singleton_iff.mpr hH)

/-- In the reduced coherent mark-one record, the occupied origin blowup
has actual cosupport outside the geometric strict transform. -/
theorem reduced_cusp_controlled_support_not_in_strict :
    ¬ B.cosupp ⊆ geoStrictTransform originProj ({0} : Set X) (embeddedCuspSet 5) :=
  fun h => reduced_cusp_competitor_off_geoStrict (h reduced_cusp_exceptional_competitor_active)

/-- The linear chart equation survives controlled division at the exceptional
competitor. Its restriction to the exceptional plane is a nonzero germ. -/
theorem reduced_cusp_competitor_linear_member : B.ideal.mem y w := by
  rw [show B.ideal = controlledTransform hπ A 1 from geoTransform_ideal_eq_controlledTransform rfl hA hπ,
    controlledTransform,idealPow_one_exceptionalDivisor]
  have hw : HolomorphicAt 3 w y := hqHol (1 : Fin 2)
  apply mem_colon_iff.mpr ⟨hw,?_⟩
  intro g hg
  obtain ⟨c,hc,hcEq⟩ := exists_eq_sum_compFun_of_mem_pullback hπ.contMDiff hyP hg
  let b : Y → ℂ := fun z => ∑ i : Fin 3, gen 0 (originCoord 0 z) i * c i z
  have hb : HolomorphicAt 3 b y :=
    HolomorphicAt.sum _ fun i _ => (holomorphicAt_comp_originCoord
      (F := fun z : ComplexModel 3 => gen 0 z i)
      ((contDiff_gen_coord 0 i).differentiable (by simp)) hyU).mul (hc i)
  have hgEq : g =ᶠ[𝓝 y] fun z => u z * b z := by
    filter_upwards [hcEq,(isOpen_originSource 0).mem_nhds hyU] with z hz hzU
    rw [hz,show u z * b z = ∑ i : Fin 3, u z * (gen 0 (originCoord 0 z) i * c i z) by
      unfold b; rw [Finset.mul_sum]]
    apply Finset.sum_congr rfl
    intro i _
    change originProj z i * c i z = _
    rw [originProj_apply_eq hzU i]
    ring
  let F : X → ℂ := embeddedCuspEquations 5 1
  have hF : A.mem (originProj y) F := by
    obtain ⟨D,_,h0,hgen⟩ := reduced_cusp_source_generators
    rw [hyP]
    exact (hgen 0 h0 F).mpr (inSpanAt_self (fun i => Eventually.of_forall (equations_differentiable 5 i)) 1)
  have hFh : HolomorphicAt 3 F (originProj y) :=
    Eventually.of_forall fun z => ((equations_differentiable 5 1) z).mdifferentiableAt
  have hFc : HolomorphicAt 3 (F ∘ originProj) y :=
    HolomorphicAt.comp_contMDiff hFh (Eventually.of_forall fun z => hπ.contMDiff z)
  have hBase : (GermIdeal.pullback (m := 3) originProj A).mem y (F ∘ originProj) :=
    GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨F,hF,rfl⟩ hFc)
  have hCoherent := isCoherent_pullback hπ.contMDiff hA
  apply mem_of_isInSpanAt_mem hCoherent
  refine ⟨(GermIdeal.IsInvertible.holomorphicAt_mem (exceptionalDivisor hπ).isInvertible hg).mul hw,
    1,fun _ => F ∘ originProj, fun _ => b,fun _ => hBase,fun _ => hb,?_⟩
  filter_upwards [hgEq,(isOpen_originSource 0).mem_nhds hyU] with z hz hzU
  rw [Fin.sum_univ_one,hz]
  change u z * b z * w z = b z * embeddedCuspEquations 5 1 (originProj z)
  rw [total_equation_factor z hzU (1 : Fin 2)]
  change u z * b z * w z = b z * (u z * w z)
  ring

private theorem competitor_boundary_linear_nonzero :
    ∃ᶠ z in 𝓝 y, z ∈ (originProj ⁻¹' ({0} : Set X)) ∧ w z ≠ 0 := by
  let a : ℂ → ComplexModel 3 := fun t =>
    PiLp.single 2 (1 : Fin 3) (1 : ℂ) + t • PiLp.single 2 (2 : Fin 3) (1 : ℂ)
  let c : ℂ → Y := fun t => originMk 0 (a t)
  have ha : Continuous a := continuous_const.add (continuous_id.smul continuous_const)
  have hMk : Continuous (originMk (0 : Fin 3)) :=
    continuousOn_univ.mp (originHomeomorph (0 : Fin 3)).continuousOn_symm
  have hc : Continuous c := hMk.comp ha
  have hc0 : c 0 = y := by simp [c,a,y]
  apply mem_closure_iff_frequently.mp
  apply mem_closure_iff.mpr
  intro U hU hyU'
  obtain ⟨t,htU,ht⟩ := mem_closure_iff.mp ((dense_compl_singleton (0 : ℂ)) 0)
    (c ⁻¹' U) (hU.preimage hc) (show c 0 ∈ U by rwa [hc0])
  refine ⟨c t,htU,?_,?_⟩
  · change originProj (originMk 0 (a t)) = 0
    change (a t 0 • gen 0 (a t) : ComplexModel 3) = 0
    rw [show a t 0 = 0 by simp [a,show (0 : Fin 3) ≠ 1 by decide,show (0 : Fin 3) ≠ 2 by decide],zero_smul]
  · change originCoord 0 (originMk 0 (a t)) 2 ≠ 0
    rw [originCoord_originMk,show a t 2 = t from by
      simp [a,show (2 : Fin 3) ≠ 1 by decide]]
    exact fun h => ht (mem_singleton_iff.mpr h)

private theorem cuspAdvanced_wf : B.IsWellFormed := by
  have hi : cuspMarkOne.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,hA,
    isSNCDivisor_nil,SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor isSNCDivisor_nil⟩
  exact MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hi _
    reduced_cusp_origin_step_isGeoTestTower

/-- The exceptional competitor has positive original nonmonomial order.
It does not lie in the monomial branch of the original invariant. -/
theorem reduced_cusp_exceptional_competitor_positive_residual :
    0 < nmOrd B y := by
  have hBN : B.N = univ := geoTransform_N_eq_univ rfl hπ
  have hBE : B.E = [originProj ⁻¹' ({0} : Set X)] := rfl
  have hFreq : ∃ᶠ z in 𝓝 y, z ∈ B.N ∧ z ∈ originProj ⁻¹' ({0} : Set X) ∧ w z ≠ 0 :=
    competitor_boundary_linear_nonzero.mono (fun z hz => ⟨hBN.symm ▸ mem_univ z,hz⟩)
  have hExp : divExpAlong 3 B.N B.ideal (originProj ⁻¹' ({0} : Set X)) y = 0 :=
    HironakaG8E4cCompanion.divExpAlong_eq_zero_of_frequently cuspAdvanced_wf.isCoherent
      reduced_cusp_competitor_linear_member hFreq
  have hOne : (monomialPartAlong 3 B.N B.ideal B.E).mem y (fun _ => (1 : ℂ)) := by
    refine ⟨holomorphicAt_const _,fun i _ _ => ?_⟩
    have hi : B.E.get i = originProj ⁻¹' ({0} : Set X) := by
      have hMem := List.get_mem (l := B.E) i
      exact List.mem_singleton.mp ((congrArg (fun L => B.E.get i ∈ L) hBE).mp hMem)
    rw [hi,hExp,idealPow_zero]
    exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self (holomorphicAt_const 1) (holomorphicAt_const 1))
  have hOrd : y ∈ ordGe B 1 := by
    refine ⟨hBN.symm ▸ mem_univ y,fun f hf => ?_⟩
    change (colon (restrictOn 3 B.N B.ideal) (monomialPartAlong 3 B.N B.ideal B.E)).mem y f at hf
    have hMem := (mem_colon_iff.mp hf).2 _ hOne
    rw [hBN,BlowupTowerTransforms.restrictOn_univ cuspAdvanced_wf.isCoherent] at hMem
    have hfB : B.ideal.mem y f := by simpa only [one_mul] using hMem
    exact reduced_cusp_exceptional_competitor_active.2 f hfB
  obtain ⟨j,hj⟩ := cuspAdvanced_wf.isClosedSubmanifold_N.2 y hOrd.1
  obtain ⟨r,hr⟩ := exists_isLocalRetraction hj
  obtain ⟨o,ho⟩ := hr.exists_not_vanishesToOrderOn (hqHol (1 : Fin 2))
    (hFreq.mono (fun _ hz => ⟨hz.1,hz.2.2⟩))
  have hwNm : (nmPart B).mem y w := NonmonomialTransformAlong.le_nonmonomialPartAlong_self
    cuspAdvanced_wf.isCoherent y w reduced_cusp_competitor_linear_member
  exact succ_le_nmOrd_of_mem
    ⟨o,fun hm => ho ((ordGe_anti B (Nat.le_succ o) hm).2 w hwNm)⟩ hOrd

/-- The positive read is the first coordinate at the literal occupied prefix
of the original canonical invariant. -/
theorem reduced_cusp_original_competitor_first_coordinate_positive :
    0 < (ofLex ((canonicalInvariant 3).inv cuspMarkOne
      (BlowupTower.step (Z := Y) .refl ({0} : Set X) originProj hπ) y)).1 :=
  reduced_cusp_exceptional_competitor_positive_residual

/-- Fresh strict Hilbert--Samuel data cannot represent the whole controlled
record in the ordinary local weak class at this restart. -/
theorem reduced_cusp_actual_restart_not_fresh_native
    (Q : MarkedIdeal 3 Y) (H : ℕ → ℕ)
    (hQ : NativeHSState Q (geoStrictTransform originProj ({0} : Set X) (embeddedCuspSet 5)) H) :
    ¬ LocWPEquiv B Q :=
  HironakaG8ChronologicalRestartObstruction.not_locWPEquiv_fresh_native_of_active_off_strict
    hQ reduced_cusp_exceptional_competitor_active reduced_cusp_competitor_off_geoStrict

end
end Hironaka.HironakaG8ReducedCuspControlledObstruction
