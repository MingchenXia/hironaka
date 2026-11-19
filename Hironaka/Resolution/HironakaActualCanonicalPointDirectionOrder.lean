import Hironaka.Resolution.HironakaActualCanonicalTriangularShear
import Hironaka.Resolution.HironakaActualCanonicalZeroDirectionOrder
import Hironaka.Resolution.HironakaActualPointChartTransition

/-! Full actual point-strict HS equality preserves the order of each SAME original canonical reduced member. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualCanonicalPointDirectionOrder
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalStrictGenerators HironakaActualFormalBlowupAllDirections
  HironakaActualCoefficientReducedStrictGenerators HironakaActualPointCentreStrictGenerators
  HironakaActualPointUnitCoordinateChange HironakaActualCanonicalDirectionPivot
  HironakaActualCanonicalTriangularShear HironakaActualCanonicalZeroDirectionOrder
  HironakaActualConeEqualityDirectionalStability HironakaActualPointChartTransition
variable {n : ℕ}

private theorem point_weight_eq_degree (α : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight Set.univ) α=normalExponentDegree α := by
  simp [Finsupp.weight_eq_sum,actualCoordinateWeight,normalExponentDegree]

private theorem point_ideal_eq_variables :
    actualFormalCoordinateIdeal n Set.univ=genuineFormalVariables n := by
  simp only [actualFormalCoordinateIdeal,Set.image_univ,genuineFormalVariables]

/-- The actual source shear identifies normalizations of the SAME entire original series. -/
theorem actualNormalizedFormalMember_zero_centerShear (f : Fin n) (w : Fin n → ℂ)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n Set.univ ^ μ) :
    actualNormalizedFormalMember Set.univ f (mem_univ f) (fun _ => 0) μ
      (actualFormalCenterShear Set.univ f w F)
      ((mem_coordinate_power_iff_centerShear Set.univ f (mem_univ f) w μ F).mp hF)=
      actualNormalizedFormalMember Set.univ f (mem_univ f) w μ F hF := by
  symm
  apply actualNormalizedFormalMember_unique
  rw [← actualFormalBlowup_eq_zero_comp_centerShear Set.univ f (mem_univ f) w F]
  exact actualNormalizedFormalMember_spec Set.univ f (mem_univ f) w μ F hF

/-- BOTH whole strict-ideal directions follow from genuine preimages and all original normalized members. -/
theorem actual_point_strict_zero_map_centerShear
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (f : Fin n) (w : Fin n → ℂ) :
    actualFormalStrictTransform
      (Ideal.map (actualFormalCenterShear Set.univ f w).toRingHom K)
        Set.univ f (mem_univ f) (fun _ => 0)=
      actualFormalStrictTransform K Set.univ f (mem_univ f) w := by
  rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal,
    actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
  apply le_antisymm
  · rw [actualNormalizedOriginalMemberIdeal]
    apply Ideal.span_le.mpr
    rintro G ⟨μ,H,hHK,hH,rfl⟩
    obtain ⟨F,hFK,rfl⟩ := (Ideal.mem_map_iff_of_surjective
      (actualFormalCenterShear Set.univ f w).toRingHom
      (actualFormalCenterShearAlgEquiv Set.univ f w).surjective).mp hHK
    have hF := (mem_coordinate_power_iff_centerShear Set.univ f (mem_univ f) w μ F).mpr hH
    change actualNormalizedFormalMember Set.univ f (mem_univ f) (fun _ => 0) μ
      (actualFormalCenterShear Set.univ f w F) hH ∈ _
    rw [actualNormalizedFormalMember_zero_centerShear f w μ F hF]
    exact Ideal.subset_span ⟨μ,F,hFK,hF,rfl⟩
  · rw [actualNormalizedOriginalMemberIdeal]
    apply Ideal.span_le.mpr
    rintro G ⟨μ,F,hFK,hF,rfl⟩
    have hSF := (mem_coordinate_power_iff_centerShear Set.univ f (mem_univ f) w μ F).mp hF
    have hmem : actualNormalizedFormalMember Set.univ f (mem_univ f) (fun _ => 0) μ
        (actualFormalCenterShear Set.univ f w F) hSF ∈ actualNormalizedOriginalMemberIdeal
          (Ideal.map (actualFormalCenterShear Set.univ f w).toRingHom K)
            Set.univ f (mem_univ f) (fun _ => 0) :=
      Ideal.subset_span
        ⟨μ,actualFormalCenterShear Set.univ f w F,Ideal.mem_map_of_mem _ hFK,hSF,rfl⟩
    simpa only [SetLike.mem_coe,actualNormalizedFormalMember_zero_centerShear f w μ F hF] using hmem

/-- Only genuine whole strict/source HS equality is supplied; all directional and support structure is derived internally. -/
theorem actualNormalizedReducedFormalVertex_mem_degree_power_of_point_hs_eq
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ)
    (hHS : ∀ ℓ, genuineFormalHilbertSamuelValue n
      (actualFormalStrictTransform K Set.univ e (mem_univ e) b) ℓ=
        genuineFormalHilbertSamuelValue n K ℓ)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    actualNormalizedReducedFormalVertex MonomialOrder.degLex K Set.univ e (mem_univ e) b
      (actualReducedVertexSeries_mem_point_power n K) a ∈
        genuineFormalVariables n ^ normalExponentDegree a.val := by
  let v := actualPointUnitBasePoint e b
  have hv : ∃ i, v i ≠ 0 := by
    refine ⟨e,?_⟩
    simp [v,actualPointUnitBasePoint_apply]
  have hD : ∀ F ∈ HironakaActualHomogeneousInitialHS.actualHomogeneousInitialIdeal K,
      (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i F) ∈
        HironakaActualHomogeneousInitialHS.actualHomogeneousInitialIdeal K :=
    actual_homogeneous_initial_directional_stable_of_point_strict_hs_eq K e b hHS
  obtain ⟨f,hvf,hmax,hvertices,_⟩ := exists_initial_direction_cylindrical_coordinate K v hv hD
  let w : Fin n → ℂ := fun i => v i/v f
  have htri : ∀ i : Fin n, i ≠ f → w i ≠ 0 →
      MonomialOrder.degLex.toSyn (Finsupp.single i 1) <
        MonomialOrder.degLex.toSyn (Finsupp.single f 1) := by
    intro i hif hwi
    have hvi : v i ≠ 0 := by
      intro hz
      exact hwi (by simp only [w,hz,zero_div])
    apply lt_of_le_of_ne (hmax i hvi)
    intro he
    exact hif (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)
      (MonomialOrder.degLex.toSyn.injective he))
  let KS := Ideal.map (actualFormalCenterShear Set.univ f w).toRingHom K
  have hSvariables : Ideal.map (actualFormalCenterShearAlgEquiv Set.univ f w).toRingEquiv.toRingHom
      (genuineFormalVariables n)=genuineFormalVariables n := by
    have hhom : (actualFormalCenterShearAlgEquiv Set.univ f w).toRingEquiv.toRingHom=
        (actualFormalCenterShear Set.univ f w).toRingHom := by
      ext F
      rfl
    rw [hhom,← point_ideal_eq_variables]
    exact map_coordinateIdeal_centerShear Set.univ f (mem_univ f) w
  have hHSzero : ∀ ℓ, genuineFormalHilbertSamuelValue n
      (actualFormalStrictTransform KS Set.univ f (mem_univ f) (fun _ => 0)) ℓ=
        genuineFormalHilbertSamuelValue n KS ℓ := by
    intro ℓ
    calc
      _=genuineFormalHilbertSamuelValue n
          (actualFormalStrictTransform K Set.univ f (mem_univ f) w) ℓ := by
        dsimp only [KS]
        rw [actual_point_strict_zero_map_centerShear K f w]
      _=genuineFormalHilbertSamuelValue n
          (actualFormalStrictTransform K Set.univ e (mem_univ e) b) ℓ :=
        genuineFormalHilbertSamuelValue_original_point_chart_transition K e b f hvf ℓ
      _=genuineFormalHilbertSamuelValue n K ℓ := hHS ℓ
      _=genuineFormalHilbertSamuelValue n KS ℓ :=
        genuineFormalHilbertSamuelValue_map_formalAlgEquiv
          (actualFormalCenterShearAlgEquiv Set.univ f w) hSvariables K ℓ
  let aS := actualCenterShearVertex MonomialOrder.degLex K f w htri a
  have hz := actualNormalizedReducedFormalVertex_zero_mem_degree_power_of_hs_eq KS f hHSzero aS
  have hcanonical := actualFormalCenterShear_actualReducedVertexSeries
    MonomialOrder.degLex K f w htri hvertices a
  let μ := normalExponentDegree a.val
  let R := actualReducedVertexSeries MonomialOrder.degLex K a
  have hR : R ∈ actualFormalCoordinateIdeal n Set.univ ^ μ := by
    simpa only [point_weight_eq_degree] using actualReducedVertexSeries_mem_point_power n K a
  have hzero : actualNormalizedFormalMember Set.univ f (mem_univ f) (fun _ => 0) μ
      (actualFormalCenterShear Set.univ f w R)
      ((mem_coordinate_power_iff_centerShear Set.univ f (mem_univ f) w μ R).mp hR) ∈
        genuineFormalVariables n ^ μ := by
    let V := actualNormalizedReducedFormalVertex MonomialOrder.degLex KS Set.univ f
      (mem_univ f) (fun _ => 0) (actualReducedVertexSeries_mem_point_power n KS) aS
    have hspec : (MvPowerSeries.X f) ^
        Finsupp.weight (actualCoordinateWeight Set.univ) aS.val * V=
          actualFormalBlowup Set.univ f (fun _ => 0)
            (actualReducedVertexSeries MonomialOrder.degLex KS aS) :=
      actualNormalizedFormalMember_spec Set.univ f (mem_univ f) (fun _ => 0) _
        (actualReducedVertexSeries MonomialOrder.degLex KS aS)
        (actualReducedVertexSeries_mem_point_power n KS aS)
    rw [point_weight_eq_degree,← hcanonical] at hspec
    have hVN : V=actualNormalizedFormalMember Set.univ f (mem_univ f) (fun _ => 0) μ
        (actualFormalCenterShear Set.univ f w R)
        ((mem_coordinate_power_iff_centerShear Set.univ f (mem_univ f) w μ R).mp hR) :=
      actualNormalizedFormalMember_unique Set.univ f (mem_univ f) (fun _ => 0) μ
        (actualFormalCenterShear Set.univ f w R) _ V hspec
    have hV : V ∈ genuineFormalVariables n ^ μ := hz
    rwa [hVN] at hV
  have hw : actualNormalizedFormalMember Set.univ f (mem_univ f) w μ R hR ∈
      genuineFormalVariables n ^ μ := by
    rwa [actualNormalizedFormalMember_zero_centerShear f w μ R hR] at hzero
  have he : actualNormalizedFormalMember Set.univ e (mem_univ e) b μ R hR ∈
      genuineFormalVariables n ^ μ :=
    (actualPointOriginalChartTransition_normalized_mem_power_iff e b f hvf μ R hR μ).mpr hw
  let V := actualNormalizedReducedFormalVertex MonomialOrder.degLex K Set.univ e (mem_univ e) b
    (actualReducedVertexSeries_mem_point_power n K) a
  have hspec : (MvPowerSeries.X e) ^
      Finsupp.weight (actualCoordinateWeight Set.univ) a.val * V=actualFormalBlowup Set.univ e b R :=
    actualNormalizedFormalMember_spec Set.univ e (mem_univ e) b _
      (actualReducedVertexSeries MonomialOrder.degLex K a) (actualReducedVertexSeries_mem_point_power n K a)
  rw [point_weight_eq_degree] at hspec
  have hVN : V=actualNormalizedFormalMember Set.univ e (mem_univ e) b μ R hR :=
    actualNormalizedFormalMember_unique Set.univ e (mem_univ e) b μ R hR V hspec
  change V ∈ genuineFormalVariables n ^ μ
  rw [hVN]
  exact he

end
end Hironaka.HironakaActualCanonicalPointDirectionOrder
