import Hironaka.Resolution.HironakaG1NativeCrossingGeometry
import Hironaka.Resolution.HironakaG1NativePrincipalBoundaryRatio
import Hironaka.Resolution.HironakaActualInheritedNextBlockGraph
import Hironaka.Resolution.HironakaSmoothSubmersionComposition
import Hironaka.Resolution.HironakaG1WeightedChartTransport
import Hironaka.Resolution.HironakaActualOriginalInitialHSPhase

/-! The whole two-axis analytic stalk and its actual raw boundary exponent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold

namespace Hironaka.HironakaG1NativeCrossingIdeal
noncomputable section

open HolGerm Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaG1NativeCrossingGeometry HironakaSmoothSubmersionComposition
  HironakaSmoothSubmersionGermIdealColon HironakaActualAnalyticBlockGraphTranslation
  HironakaActualInheritedNextBlockGraph HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetChartInvariance HironakaActualCoefficientPresentationCentrePower
  HironakaActualOriginalFormalHSTransfer HironakaActualFormalInitialDiagram
  HironakaRelativeNormalMonomialBasis HironakaActualNormalZeroAnalyticSaturation
  HironakaG1CarrierPowerReduction DivisorExponent DivisorExponentAlong IdealWeightPowers GermIdealOrder GermIdealPullbackCalculus BlowupTowers
  HironakaG1WeightedChartTransport HironakaG1NativePrincipalBoundaryRatio
  HironakaActualWeightedCoefficientCompression HironakaActualFixedFlatteningHSComparison
  HironakaActualNativeSourceChartComposition HironakaActualOriginalInitialHSPhase
  HironakaActualHistoricalHSMarkedDomain HironakaActualPrescribedCentreRebasing
  HironakaRelativeNormalDeformationInitialRelations

abbrev Φ := centeredCoordinates (n := 2) origin
abbrev hΦ := centeredCoordinates_zero (n := 2) origin

def axisProductGerm : HolGerm (ComplexModel 2) := coordinateGerm 0 * coordinateGerm 1

private theorem coordinate_ne_zero (i : Fin 2) : coordinateGerm i ≠ 0 := by
  intro h
  have h' := congrArg (actualUnshiftedTaylorAlgHom 2) h
  rw [actualUnshiftedTaylor_coordinate, map_zero] at h'
  have hCoeff := congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h'
  simp [MvPowerSeries.coeff_X] at hCoeff

theorem axisProductGerm_ne_zero : axisProductGerm ≠ 0 :=
  mul_ne_zero (coordinate_ne_zero 0) (coordinate_ne_zero 1)

private theorem adapted_origin_mk (F : M → ℂ) (hF : HolomorphicAt 2 F origin) :
    adaptedGerm origin Φ hΦ F hF =
      HolGerm.mk (fun z => F (ULift.up z)) (by
        have he : (fun w => F ((chartAt (ComplexModel 2) origin).symm (Φ.invFun w))) =
            (fun w => F (ULift.up w)) := by
          funext w
          change F (ULift.up (w+0)) = _
          rw [add_zero]
        rw [← he]
        exact (holomorphic_adapted_iff origin Φ hΦ F).mpr hF) := by
  apply HolGerm.mk_eq_mk_iff.mpr
  apply Eventually.of_forall
  intro z
  change F (ULift.up (z + 0)) = F (ULift.up z)
  rw [add_zero]

private theorem axisGerm_projection_zero (i : Fin 2) (F : M → ℂ)
    (hF : (vanishingIdeal (n := 2) (axis i)).mem origin F) :
    actualBlockProjectionGermHom ({i}ᶜ : Set (Fin 2))
      (adaptedGerm origin Φ hΦ F hF.1) = 0 := by
  rw [adapted_origin_mk, actualBlockProjectionGermHom, compAlgHom_mk, ← HolGerm.mk_zero]
  apply HolGerm.mk_eq_mk_iff.mpr
  let p (z : ComplexModel 2) : M := ULift.up (actualBlockCoordinateProjection ({i}ᶜ : Set (Fin 2)) z)
  have hP : Tendsto p (𝓝 (0 : ComplexModel 2)) (𝓝 origin) := by
    have hc : Continuous p :=
      continuous_uliftUp.comp (actualBlockCoordinateProjection ({i}ᶜ : Set (Fin 2))).continuous
    have hp0 : p 0 = origin := congrArg ULift.up (map_zero _)
    exact hp0 ▸ hc.tendsto 0
  filter_upwards [hP.eventually hF.2] with z hz
  apply hz
  change actualBlockCoordinateProjection ({i}ᶜ : Set (Fin 2)) z i = 0
  simp [actualBlockCoordinateProjection_apply]

private theorem adapted_origin_coordinate (i : Fin 2) :
    ∃ (hF : HolomorphicAt 2 (fun z : M => z.down i) origin),
      adaptedGerm origin Φ hΦ (fun z : M => z.down i) hF = coordinateGerm i := by
  have hF : HolomorphicAt 2 (fun z : M => z.down i) origin := by
    apply (holomorphic_adapted_iff origin Φ hΦ _).mp
    have he : (fun z => (((chartAt (ComplexModel 2) origin).symm (Φ.invFun z)) : M).down i) =
        fun z : ComplexModel 2 => z i := by
      funext z
      change (z + 0) i = z i
      rw [add_zero]
    rw [he]
    exact Eventually.of_forall (fun z => (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt (x := z))
  refine ⟨hF,?_⟩
  rw [adapted_origin_mk]
  rfl

private theorem coordinateBlock_singleton (i : Fin 2) :
    actualAnalyticCoordinateBlockIdeal ({i} : Set (Fin 2)) = Ideal.span {coordinateGerm i} := by
  rw [actualAnalyticCoordinateBlockIdeal, Set.image_singleton]

theorem adapted_origin_axis (i : Fin 2) :
    adaptedIdeal (vanishingIdeal (n := 2) (axis i)) origin Φ hΦ =
      Ideal.span {coordinateGerm i} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨F,hF,hMem,rfl⟩
    rw [← coordinateBlock_singleton]
    exact (mem_actualAnalyticCoordinateBlockIdeal_iff_projection_zero _ _).mpr
      (axisGerm_projection_zero i F hMem)
  · apply Ideal.span_le.mpr
    rintro _ ⟨rfl⟩
    obtain ⟨hF,hEq⟩ := adapted_origin_coordinate i
    exact Ideal.subset_span ⟨_,hF,⟨hF,Eventually.of_forall (fun _ hy => hy)⟩,hEq.symm⟩

/-- The *whole* original vanishing stalk of the analytic crossing is the
principal product ideal in the actual centered source chart. -/
theorem adapted_origin_crossing :
    adaptedIdeal (vanishingIdeal (n := 2) crossing) origin Φ hΦ =
      Ideal.span {axisProductGerm} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨F,hF,hMem,rfl⟩
    have hAxis (i : Fin 2) : (vanishingIdeal (n := 2) (axis i)).mem origin F :=
      ⟨hF,hMem.2.mono (fun y h hy => h (Fin.cases (fun h => Or.inl h)
        (fun j h => by obtain rfl := Fin.eq_zero j; exact Or.inr h) i hy))⟩
    have hA : adaptedGerm origin Φ hΦ F hF ∈ adaptedIdeal (vanishingIdeal (n := 2) (axis 0)) origin Φ hΦ :=
      Ideal.subset_span ⟨F,hF,hAxis 0,rfl⟩
    rw [adapted_origin_axis] at hA
    obtain ⟨G,hG⟩ := Ideal.mem_span_singleton.mp hA
    have hK : actualBlockProjectionGermHom ({(1 : Fin 2)}ᶜ : Set (Fin 2)) (coordinateGerm 0 * G) = 0 :=
      hG ▸ axisGerm_projection_zero 1 F (hAxis 1)
    rw [map_mul, actualBlockProjectionGermHom_coordinate, if_pos (by decide)] at hK
    have hKG := (mul_eq_zero.mp hK).resolve_left (coordinate_ne_zero 0)
    have hKG' := (mem_actualAnalyticCoordinateBlockIdeal_iff_projection_zero {(1 : Fin 2)} G).mpr hKG
    rw [coordinateBlock_singleton] at hKG'
    obtain ⟨R,hR⟩ := Ideal.mem_span_singleton.mp hKG'
    apply Ideal.mem_span_singleton.mpr
    exact ⟨R,by rw [hG,hR,axisProductGerm,mul_assoc]⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨rfl⟩
    obtain ⟨h0,hG0⟩ := adapted_origin_coordinate 0
    obtain ⟨h1,hG1⟩ := adapted_origin_coordinate 1
    let F : M → ℂ := fun z => z.down 0 * z.down 1
    have hF : HolomorphicAt 2 F origin := h0.mul h1
    have hMem : (vanishingIdeal (n := 2) crossing).mem origin F := by
      refine ⟨hF,Eventually.of_forall fun y hy => ?_⟩
      rcases hy with h | h
      · exact mul_eq_zero.mpr (Or.inl h)
      · exact mul_eq_zero.mpr (Or.inr h)
    refine Ideal.subset_span ⟨F,hF,hMem,?_⟩
    have he := adaptedGerm_mul origin Φ hΦ _ _ h1 h0
    exact (he.trans (congrArg₂ (· * ·) hG0 hG1)).symm

/-- The actual product germ has exact local analytic order two. -/
theorem axisProductGerm_exact_order :
    axisProductGerm ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel 2)) ^ 2 ∧
    axisProductGerm ∉ IsLocalRing.maximalIdeal (HolGerm (ComplexModel 2)) ^ 3 := by
  let β : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1
  have hβ : normalExponentDegree β = 2 := by
    simp [β, normalExponentDegree, Fin.sum_univ_two]
  have hT : actualUnshiftedTaylorAlgHom 2 axisProductGerm = MvPowerSeries.monomial β 1 := by
    rw [axisProductGerm,map_mul,actualUnshiftedTaylor_coordinate,actualUnshiftedTaylor_coordinate]
    simp only [MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, one_mul, β]
  have hMem (d : ℕ) : axisProductGerm ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel 2)) ^ d ↔
      MvPowerSeries.monomial β (1 : ℂ) ∈ genuineFormalVariables 2 ^ d := by
    rw [← hT, ← map_actualUnshifted_maximal_pow]
    exact mem_analytic_ideal_iff_actualUnshifted_extension 2 _ _
  constructor
  · apply (hMem 2).mpr
    apply (mem_genuineFormalVariables_pow_iff_coefficients_zero 2 2 _).mpr
    intro a ha
    have ha' : a ≠ β := by intro h; rw [h,hβ] at ha; omega
    simp [MvPowerSeries.coeff_monomial,ha']
  · intro h
    have hZ := (mem_genuineFormalVariables_pow_iff_coefficients_zero 2 3 _).mp
      ((hMem 3).mp h) β (by rw [hβ]; decide)
    simp at hZ

/-- The original reduced crossing ideal has boundary exponent exactly one
along the genuine axis, before any marked compression. -/
theorem crossing_axis_exponent_one :
    divExpAlong 2 univ (vanishingIdeal (n := 2) crossing) (axis 0) origin = 1 := by
  classical
  let I := vanishingIdeal (n := 2) crossing
  let A := vanishingIdeal (n := 2) (axis 0)
  have hI := CartanIrreducible.cartanCoherence crossing crossing_analytic
  have hA := CartanIrreducible.cartanCoherence (axis 0) (axis_analytic 0)
  have hH := axis_regular 0 (origin_mem_axis 0)
  have hOne : IsDivNear 2 I (axis 0) 1 origin := by
    have hHol : ∀ x F, I.mem x F → HolomorphicAt 2 F x := fun _ _ h => h.1
    unfold IsDivNear
    rw [cosupport_one hHol,univ_inter,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal crossing_analytic.isClosed]
    exact Eventually.of_forall (fun _ h => Or.inl h)
  have hNotTwo : ¬ IsDivNear 2 I (axis 0) 2 origin := by
    intro hd
    obtain ⟨F,hF,hG⟩ := exists_original_adapted_representative origin Φ hΦ axisProductGerm
    have hFmem : I.mem origin F := (mem_adaptedIdeal_iff I hI origin Φ hΦ F hF).mp (by
      rw [hG]
      change axisProductGerm ∈ adaptedIdeal (vanishingIdeal (n := 2) crossing) origin Φ hΦ
      rw [adapted_origin_crossing]
      exact Ideal.mem_span_singleton_self _)
    have hg := (mem_adaptedIdeal_iff _ (isCoherent_idealPow hA 2) origin Φ hΦ F hF).mpr
      ((isDivNear_iff hI hH).mp hd F hFmem)
    rw [hG, adaptedIdeal_power_exact (X := CMfd.of (n := 2) M) A hA origin Φ hΦ] at hg
    change axisProductGerm ∈ (adaptedIdeal (vanishingIdeal (n := 2) (axis 0)) origin Φ hΦ)^2 at hg
    rw [adapted_origin_axis, Ideal.span_singleton_pow] at hg
    obtain ⟨J,hJ⟩ := Ideal.mem_span_singleton.mp hg
    have hEq : coordinateGerm 1 = coordinateGerm 0 * J := by
      apply mul_left_cancel₀ (coordinate_ne_zero 0)
      rw [← axisProductGerm,hJ,pow_two,mul_assoc]
    have hZero := congrArg (actualBlockProjectionGermHom ({(0 : Fin 2)}ᶜ : Set (Fin 2))) hEq
    rw [map_mul, actualBlockProjectionGermHom_coordinate, if_pos (by decide),
      actualBlockProjectionGermHom_coordinate, if_neg (by decide), zero_mul] at hZero
    exact coordinate_ne_zero 1 hZero
  rw [divExpAlong_univ]
  have hEx : ∃ j, ¬ IsDivNear 2 I (axis 0) (j+1) origin := ⟨1,hNotTwo⟩
  change divExp 2 I (axis 0) origin = 1
  unfold divExp
  rw [dif_pos hEx]
  exact (Nat.find_eq_iff hEx).mpr ⟨hNotTwo, fun j hj => by
    have : j = 0 := by omega
    subst j
    exact not_not_intro hOne⟩

/-- Every actual flattened chart of the original crossing has one genuine
canonical Taylor vertex, whose intrinsic weight is exactly two. -/
theorem crossing_adapted_canonical_mark_two
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel 2) origin origin))
    (hΘ : Θ.toFun (chartAt (ComplexModel 2) origin origin) = 0) :
    let I := adaptedIdeal (vanishingIdeal (n := 2) crossing) origin Θ hΘ
    let V := actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal 2 I)
    weightedCommonMark (fun v : V => normalExponentDegree v.val) = 2 ∧
      ∀ v : V, normalExponentDegree v.val = 2 := by
  let e := adaptedChartGermEquiv (X := CMfd.of (n := 2) M) origin Φ Θ hΦ hΘ
  let F := e axisProductGerm
  have hF : F ≠ 0 := fun h => axisProductGerm_ne_zero (e.injective (h.trans (map_zero e).symm))
  have hIde := map_adaptedIdeal_transition (X := CMfd.of (n := 2) M)
    (vanishingIdeal (n := 2) crossing) origin Φ Θ hΦ hΘ
  change Ideal.map e.toRingEquiv.toRingHom
    (adaptedIdeal (vanishingIdeal (n := 2) crossing) origin Φ hΦ) =
    adaptedIdeal (vanishingIdeal (n := 2) crossing) origin Θ hΘ at hIde
  rw [adapted_origin_crossing,Ideal.map_span,Set.image_singleton] at hIde
  have hIde' : adaptedIdeal (vanishingIdeal (n := 2) crossing) origin Θ hΘ = Ideal.span {F} :=
    hIde.symm
  have hFpower (p : ℕ) : F ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel 2))^p ↔
      axisProductGerm ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel 2))^p := by
    have hMap : Ideal.map e.toRingEquiv.toRingHom
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel 2))^p) =
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel 2))^p := by
      rw [Ideal.map_pow]
      change Ideal.map e.toRingEquiv (IsLocalRing.maximalIdeal (HolGerm (ComplexModel 2))) ^ p = _
      rw [IsLocalRing.map_ringEquiv_maximalIdeal]
    have hEq (g : HolGerm (ComplexModel 2)) : g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel 2)) ^ p ↔
        g ∈ Ideal.map e.toRingEquiv.toRingHom (IsLocalRing.maximalIdeal (HolGerm (ComplexModel 2)) ^ p) := by rw [hMap]
    rw [hEq F]
    constructor
    · intro h
      obtain ⟨G,hG,hEq⟩ := (Ideal.mem_map_iff_of_surjective _ e.surjective).mp h
      exact e.injective hEq ▸ hG
    · exact fun h => Ideal.mem_map_of_mem _ h
  let T := actualUnshiftedTaylorAlgHom 2 F
  have hT : T ≠ 0 := fun h => hF
    (HironakaActualAnalyticFormalNormalPowers.actualUnshiftedTaylorAlgHom_injective 2
      (h.trans (map_zero _).symm))
  have hTaylor (p : ℕ) : T ∈ genuineFormalVariables 2 ^ p ↔
      F ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel 2)) ^ p := by
    rw [← map_actualUnshifted_maximal_pow]
    exact (mem_analytic_ideal_iff_actualUnshifted_extension 2 _ F).symm
  let v := actualInitialExponent MonomialOrder.degLex T hT
  have h2 : 2 ≤ normalExponentDegree v :=
    (mem_formal_variables_pow_iff_degree_initialExponent T hT 2).mp
      ((hTaylor 2).mpr ((hFpower 2).mpr axisProductGerm_exact_order.1))
  have h3 : ¬ 3 ≤ normalExponentDegree v := by
    intro h
    exact axisProductGerm_exact_order.2 ((hFpower 3).mp ((hTaylor 3).mp
      ((mem_formal_variables_pow_iff_degree_initialExponent T hT 3).mpr h)))
  have hv : normalExponentDegree v = 2 := by omega
  dsimp only
  rw [hIde', analyticPrincipal_initial_vertices hF]
  let u : ({v} : Finset (Fin 2 →₀ ℕ)) := ⟨v,Finset.mem_singleton_self v⟩
  have hu (z : ({v} : Finset (Fin 2 →₀ ℕ))) : z = u :=
    Subtype.ext (Finset.mem_singleton.mp z.property)
  refine ⟨?_,fun z => by rw [hu z]; exact hv⟩
  unfold weightedCommonMark
  rw [Finset.prod_eq_single u]
  · exact hv
  · intro z _ hz
    exact (hz (hu z)).elim
  · intro h
    exact (h (Finset.mem_univ u)).elim

#print axioms adapted_origin_crossing
#print axioms axisProductGerm_exact_order
#print axioms crossing_axis_exponent_one
#print axioms crossing_adapted_canonical_mark_two

end
end Hironaka.HironakaG1NativeCrossingIdeal
