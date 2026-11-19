import Hironaka.Resolution.HironakaActualCanonicalNormalZeroDirectionOrder
import Hironaka.Resolution.HironakaActualCanonicalPointDirectionOrder
import Hironaka.Resolution.HironakaActualNormalCentreChartTransition

/-! Genuine normal-only shears and chart transitions return the zero-chart
order theorem to each SAME original canonical member in an arbitrary normal
chart. All source direction and cylinder data are derived internally. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualCanonicalNormalDirectionOrder
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalStrictGenerators HironakaActualFormalBlowupAllDirections
  HironakaActualCoefficientReducedStrictGenerators HironakaActualHomogeneousInitialHS
  HironakaActualTangentInitialVertices HironakaActualPointUnitCoordinateChange
  HironakaActualCanonicalVertexDirectionalInvariance HironakaActualCanonicalDirectionPivot
  HironakaActualCanonicalTriangularShear HironakaActualNormalCentreChartTransition
  HironakaActualPointChartTransition
  HironakaActualRelativeStandardnessNormalPointBridge HironakaActualCanonicalNormalZeroDirectionOrder
variable {n : ℕ}

/-- With zero tangent direction the existing full triangular shear IS the
actual normal-only shear. This is genuine whole substitution equality. -/
theorem actualFormalCenterShear_normal_eq_point
    (A : Set (Fin n)) (f : Fin n) (w : Fin n → ℂ) (hw : ∀ i ∉ A, w i = 0) :
    actualFormalCenterShear A f w = actualFormalCenterShear Set.univ f w := by
  have hc : actualFormalCenterShearCoordinates A f w =
      actualFormalCenterShearCoordinates Set.univ f w := by
    funext i
    by_cases hi : i ∈ A
    · simp only [actualFormalCenterShearCoordinates, Set.mem_sdiff, Set.mem_univ,
        true_and, hi, true_and]
    · simp [actualFormalCenterShearCoordinates, hi, hw i hi]
  apply AlgHom.ext
  intro F
  simp only [actualFormalCenterShear, MvPowerSeries.substAlgHom_apply]
  exact congrArg (fun c => MvPowerSeries.subst c F) hc

/-- The actual selected-centre factorization identifies SAME-numerator
normalizations, preserving the original normal mark. -/
theorem actualNormalizedFormalMember_normal_zero_centerShear
    (A : Set (Fin n)) (f : Fin n) (hf : f ∈ A) (w : Fin n → ℂ)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ) :
    actualNormalizedFormalMember A f hf (fun _ => 0) μ (actualFormalCenterShear A f w F)
      ((mem_coordinate_power_iff_centerShear A f hf w μ F).mp hF) =
      actualNormalizedFormalMember A f hf w μ F hF := by
  symm
  apply actualNormalizedFormalMember_unique
  rw [← actualFormalBlowup_eq_zero_comp_centerShear A f hf w F]
  exact actualNormalizedFormalMember_spec A f hf w μ F hF

/-- Both WHOLE strict-ideal inclusions use ALL genuine normalized original
members and actual inverse source shears, never a desired presentation equality. -/
theorem actual_normal_strict_zero_map_centerShear
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n))
    (f : Fin n) (hf : f ∈ A) (w : Fin n → ℂ) :
    actualFormalStrictTransform (Ideal.map (actualFormalCenterShear A f w).toRingHom K)
      A f hf (fun _ => 0) = actualFormalStrictTransform K A f hf w := by
  rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal,
    actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
  apply le_antisymm
  · rw [actualNormalizedOriginalMemberIdeal]
    apply Ideal.span_le.mpr
    rintro G ⟨μ, H, hHK, hH, rfl⟩
    obtain ⟨F, hFK, rfl⟩ := (Ideal.mem_map_iff_of_surjective
      (actualFormalCenterShear A f w).toRingHom
      (actualFormalCenterShearAlgEquiv A f w).surjective).mp hHK
    have hF := (mem_coordinate_power_iff_centerShear A f hf w μ F).mpr hH
    change actualNormalizedFormalMember A f hf (fun _ => 0) μ
      (actualFormalCenterShear A f w F) hH ∈ _
    rw [actualNormalizedFormalMember_normal_zero_centerShear A f hf w μ F hF]
    exact Ideal.subset_span ⟨μ, F, hFK, hF, rfl⟩
  · rw [actualNormalizedOriginalMemberIdeal]
    apply Ideal.span_le.mpr
    rintro G ⟨μ, F, hFK, hF, rfl⟩
    have hSF := (mem_coordinate_power_iff_centerShear A f hf w μ F).mp hF
    have hmem : actualNormalizedFormalMember A f hf (fun _ => 0) μ
        (actualFormalCenterShear A f w F) hSF ∈ actualNormalizedOriginalMemberIdeal
          (Ideal.map (actualFormalCenterShear A f w).toRingHom K) A f hf (fun _ => 0) :=
      Ideal.subset_span
        ⟨μ, actualFormalCenterShear A f w F, Ideal.mem_map_of_mem _ hFK, hSF, rfl⟩
    simpa only [SetLike.mem_coe,
      actualNormalizedFormalMember_normal_zero_centerShear A f hf w μ F hF] using hmem

private theorem blowup_eq_of_normal_direction (A : Set (Fin n)) (e : Fin n)
    (b c : Fin n → ℂ) (hbc : ∀ i ∈ A, i ≠ e → b i = c i) :
    actualFormalBlowup A e b = actualFormalBlowup A e c := by
  have hc : actualFormalBlowupCoordinates A e b = actualFormalBlowupCoordinates A e c := by
    funext i
    by_cases hi : i ∈ A
    · by_cases hie : i = e
      · simp [actualFormalBlowupCoordinates, hie]
      · simp only [actualFormalBlowupCoordinates, if_pos hi, if_neg hie, hbc i hi hie]
    · simp only [actualFormalBlowupCoordinates, if_neg hi]
  apply AlgHom.ext
  intro F
  simp only [actualFormalBlowup, MvPowerSeries.substAlgHom_apply]
  exact congrArg (fun d => MvPowerSeries.subst d F) hc

private theorem normalized_eq_of_normal_direction (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b c : Fin n → ℂ) (hbc : ∀ i ∈ A, i ≠ e → b i = c i)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ) :
    actualNormalizedFormalMember A e he b μ F hF = actualNormalizedFormalMember A e he c μ F hF := by
  apply actualNormalizedFormalMember_unique
  rw [← blowup_eq_of_normal_direction A e b c hbc]
  exact actualNormalizedFormalMember_spec A e he b μ F hF

private theorem strict_eq_of_normal_direction (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b c : Fin n → ℂ) (hbc : ∀ i ∈ A, i ≠ e → b i = c i) :
    actualFormalStrictTransform K A e he b = actualFormalStrictTransform K A e he c := by
  rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal,
    actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
  unfold actualNormalizedOriginalMemberIdeal
  simp_rw [normalized_eq_of_normal_direction A e he b c hbc]

private theorem centerShearVertex_surjective
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (f : Fin n) (w : Fin n → ℂ)
    (htri : ∀ i : Fin n, i ≠ f → w i ≠ 0 →
      MonomialOrder.degLex.toSyn (Finsupp.single i 1) <
        MonomialOrder.degLex.toSyn (Finsupp.single f 1)) :
    Function.Surjective (actualCenterShearVertex MonomialOrder.degLex K f w htri) := by
  rintro ⟨a, ha⟩
  refine ⟨⟨a, ?_⟩, Subtype.ext rfl⟩
  simpa only [actualInitialVertices, actualInitialDiagram_map_centerShear MonomialOrder.degLex K f w htri]
    using ha

/-- Only the original source tangent stability, SAME canonical centre powers,
and actual whole normal strict/source HS equality are inputs. The direction,
pivot, sheared-source stability, jet separation and SAME marked orders are
produced internally. This is not a claim about arbitrary analytic lifts. -/
theorem actualNormalizedReducedFormalVertex_mem_degree_power_of_normal_hs_eq
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hD : ∀ i ∉ A, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal K)
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex K,
      actualReducedVertexSeries MonomialOrder.degLex K a ∈ actualFormalCoordinateIdeal n A ^
        Finsupp.weight (actualCoordinateWeight A) a.val)
    (hHS : ∀ ℓ : ℕ, genuineFormalHilbertSamuelValue n (actualFormalStrictTransform K A e he b) ℓ =
      genuineFormalHilbertSamuelValue n K ℓ)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    actualNormalizedReducedFormalVertex MonomialOrder.degLex K A e he b hV a ∈
      genuineFormalVariables n ^ normalExponentDegree a.val := by
  let v : Fin n → ℂ := fun i => actualPointUnitBasePoint e (actualNormalPointDirection A b) i
  have hve : v e = 1 := by simp only [v, actualPointUnitBasePoint_apply, if_true]
  have hv : ∃ i, v i ≠ 0 := ⟨e, by rw [hve]; exact one_ne_zero⟩
  have hvA (i : Fin n) (hi : i ∉ A) : v i = 0 := by
    have hie : i ≠ e := by intro h; subst i; exact hi he
    simp only [v, actualPointUnitBasePoint_apply, if_neg hie, actualNormalPointDirection, if_neg hi]
  have hvb : ∀ i ∈ A, i ≠ e → v i = b i := by
    intro i hi hie
    simp only [v, actualPointUnitBasePoint_apply, if_neg hie, actualNormalPointDirection, if_pos hi]
  have hDir : ∀ F ∈ actualHomogeneousInitialIdeal K,
      (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i F) ∈ actualHomogeneousInitialIdeal K :=
    actual_homogeneous_initial_normal_directional_stable_of_hs_eq K A e he b hD hV hHS
  obtain ⟨f, hvf, hmax, hvertices, _⟩ := exists_initial_direction_cylindrical_coordinate K v hv hDir
  have hfA : f ∈ A := by
    by_contra h
    exact hvf (hvA f h)
  let w : Fin n → ℂ := fun i => v i / v f
  have hwA : ∀ i ∉ A, w i = 0 := by intro i hi; simp only [w, hvA i hi, zero_div]
  have htri : ∀ i : Fin n, i ≠ f → w i ≠ 0 →
      MonomialOrder.degLex.toSyn (Finsupp.single i 1) <
        MonomialOrder.degLex.toSyn (Finsupp.single f 1) := by
    intro i hif hwi
    have hvi : v i ≠ 0 := by
      intro hz
      exact hwi (by simp only [w, hz, zero_div])
    apply lt_of_le_of_ne (hmax i hvi)
    intro h
    exact hif (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)
      (MonomialOrder.degLex.toSyn.injective h))
  have hS := actualFormalCenterShear_normal_eq_point A f w hwA
  let KS := Ideal.map (actualFormalCenterShear Set.univ f w).toRingHom K
  have hVS : ∀ aS : actualInitialVertices MonomialOrder.degLex KS,
      actualReducedVertexSeries MonomialOrder.degLex KS aS ∈ actualFormalCoordinateIdeal n A ^
        Finsupp.weight (actualCoordinateWeight A) aS.val := by
    intro aS
    obtain ⟨a, rfl⟩ := centerShearVertex_surjective K f w htri aS
    rw [← actualFormalCenterShear_actualReducedVertexSeries MonomialOrder.degLex K f w htri hvertices a]
    have hm := (mem_coordinate_power_iff_centerShear A f hfA w _
      (actualReducedVertexSeries MonomialOrder.degLex K a)).mp (hV a)
    rwa [hS] at hm
  have hvS : ∀ aS : actualInitialVertices MonomialOrder.degLex KS, ∀ i ∉ A, aS.val i = 0 := by
    intro aS i hi
    obtain ⟨a, rfl⟩ := centerShearVertex_surjective K f w htri aS
    exact actualInitialVertex_coordinate_eq_zero_of_pderiv_stable MonomialOrder.degLex
      (actualHomogeneousInitialIdeal K) i (hD i hi) (actualHomogeneousInitialVertex K a)
  have hDS := actual_tangent_initial_stability_of_pure_vertices_normal_powers KS A hvS hVS
  have hSvariables : Ideal.map (actualFormalCenterShearAlgEquiv Set.univ f w).toRingEquiv.toRingHom
      (genuineFormalVariables n) = genuineFormalVariables n := by
    have hhom : (actualFormalCenterShearAlgEquiv Set.univ f w).toRingEquiv.toRingHom =
        (actualFormalCenterShear Set.univ f w).toRingHom := by ext F; rfl
    have hpoint : actualFormalCoordinateIdeal n Set.univ = genuineFormalVariables n := by
      simp only [actualFormalCoordinateIdeal, Set.image_univ, genuineFormalVariables]
    rw [hhom, ← hpoint]
    exact map_coordinateIdeal_centerShear Set.univ f (mem_univ f) w
  have hHSzero : ∀ ℓ : ℕ, genuineFormalHilbertSamuelValue n
      (actualFormalStrictTransform KS A f hfA (fun _ => 0)) ℓ = genuineFormalHilbertSamuelValue n KS ℓ := by
    intro ℓ
    calc
      _ = genuineFormalHilbertSamuelValue n (actualFormalStrictTransform K A f hfA w) ℓ := by
        dsimp only [KS]
        rw [← hS, actual_normal_strict_zero_map_centerShear K A f hfA w]
      _ = genuineFormalHilbertSamuelValue n (actualFormalStrictTransform K A e he v) ℓ :=
        genuineFormalHilbertSamuelValue_normal_chart_transition K A e f he hfA v hve hvf ℓ
      _ = genuineFormalHilbertSamuelValue n (actualFormalStrictTransform K A e he b) ℓ := by
        rw [strict_eq_of_normal_direction K A e he v b hvb]
      _ = genuineFormalHilbertSamuelValue n K ℓ := hHS ℓ
      _ = genuineFormalHilbertSamuelValue n KS ℓ :=
        genuineFormalHilbertSamuelValue_map_formalAlgEquiv
          (actualFormalCenterShearAlgEquiv Set.univ f w) hSvariables K ℓ
  let aS := actualCenterShearVertex MonomialOrder.degLex K f w htri a
  have hz := actualNormalizedReducedFormalVertex_normal_zero_mem_degree_power_of_hs_eq KS A f hfA hDS hVS hHSzero aS
  have hcanonical := actualFormalCenterShear_actualReducedVertexSeries
    MonomialOrder.degLex K f w htri hvertices a
  let μ := normalExponentDegree a.val
  let R := actualReducedVertexSeries MonomialOrder.degLex K a
  have hR : R ∈ actualFormalCoordinateIdeal n A ^ μ := by
    simpa only [actual_normal_vertex_mark_eq_degree K A hD a] using hV a
  have hzero : actualNormalizedFormalMember A f hfA (fun _ => 0) μ
      (actualFormalCenterShear A f w R)
      ((mem_coordinate_power_iff_centerShear A f hfA w μ R).mp hR) ∈ genuineFormalVariables n ^ μ := by
    let V := actualNormalizedReducedFormalVertex MonomialOrder.degLex KS A f hfA (fun _ => 0) hVS aS
    have hspec : (MvPowerSeries.X f) ^ Finsupp.weight (actualCoordinateWeight A) aS.val * V =
        actualFormalBlowup A f (fun _ => 0) (actualReducedVertexSeries MonomialOrder.degLex KS aS) :=
      actualNormalizedFormalMember_spec A f hfA (fun _ => 0) _
        (actualReducedVertexSeries MonomialOrder.degLex KS aS) (hVS aS)
    rw [actual_normal_vertex_mark_eq_degree KS A hDS aS, ← hcanonical, ← hS] at hspec
    have hVN : V = actualNormalizedFormalMember A f hfA (fun _ => 0) μ
        (actualFormalCenterShear A f w R)
        ((mem_coordinate_power_iff_centerShear A f hfA w μ R).mp hR) :=
      actualNormalizedFormalMember_unique A f hfA (fun _ => 0) μ
        (actualFormalCenterShear A f w R) _ V hspec
    have hVorder : V ∈ genuineFormalVariables n ^ μ := hz
    rwa [hVN] at hVorder
  have hw : actualNormalizedFormalMember A f hfA w μ R hR ∈ genuineFormalVariables n ^ μ := by
    rwa [actualNormalizedFormalMember_normal_zero_centerShear A f hfA w μ R hR] at hzero
  have hnormv : actualNormalizedFormalMember A e he v μ R hR ∈ genuineFormalVariables n ^ μ :=
    (normalized_member_mem_power_iff_normal_chart_transition A e f he hfA v hve hvf μ R hR μ).mpr hw
  have hnormb : actualNormalizedFormalMember A e he b μ R hR ∈ genuineFormalVariables n ^ μ := by
    rwa [normalized_eq_of_normal_direction A e he v b hvb μ R hR] at hnormv
  let V := actualNormalizedReducedFormalVertex MonomialOrder.degLex K A e he b hV a
  have hspec : (MvPowerSeries.X e) ^ Finsupp.weight (actualCoordinateWeight A) a.val * V =
      actualFormalBlowup A e b R :=
    actualNormalizedFormalMember_spec A e he b _ (actualReducedVertexSeries MonomialOrder.degLex K a) (hV a)
  rw [actual_normal_vertex_mark_eq_degree K A hD a] at hspec
  have hVN : V = actualNormalizedFormalMember A e he b μ R hR :=
    actualNormalizedFormalMember_unique A e he b μ R hR V hspec
  change V ∈ genuineFormalVariables n ^ μ
  rw [hVN]
  exact hnormb

end
end Hironaka.HironakaActualCanonicalNormalDirectionOrder
