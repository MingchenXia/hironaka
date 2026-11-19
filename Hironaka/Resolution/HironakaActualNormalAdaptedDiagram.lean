import Hironaka.Resolution.HironakaActualNormalZeroDiagram
import Hironaka.Resolution.HironakaActualCanonicalNormalDirectionOrder

/-! Original normal strict/source HS equality internally produces an adapted
zero chart in which the SAME inherited canonical family is literally reduced.
Only the derived triangular linear shear and stable NORMAL-block permutation
are used. No covariance under an arbitrary old coordinate order or a later
nonlinear coordinate change, and no analytic history, is asserted. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualNormalAdaptedDiagram
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalStrictGenerators HironakaActualFormalBlowupAllDirections
  HironakaActualCoefficientReducedStrictGenerators
  HironakaActualHomogeneousInitialHS HironakaActualTangentInitialVertices
  HironakaActualCanonicalVertexDirectionalInvariance
  HironakaActualPointUnitCoordinateChange HironakaActualPointChartTransition
  HironakaActualCanonicalDirectionPivot HironakaActualCanonicalTriangularShear
  HironakaActualNormalCentreChartTransition HironakaActualRelativeStandardnessNormalPointBridge
  HironakaActualCanonicalNormalZeroDirectionOrder HironakaActualCanonicalNormalDirectionOrder
  HironakaActualRelativeStandardnessNormalPivotPriority HironakaActualNormalRename
  HironakaActualNormalZeroDiagram
variable {n : ℕ}

private theorem centerShearVertex_surjective
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (f : Fin (n + 1)) (w : Fin (n + 1) → ℂ)
    (htri : ∀ i : Fin (n + 1), i ≠ f → w i ≠ 0 →
      MonomialOrder.degLex.toSyn (Finsupp.single i 1) <
        MonomialOrder.degLex.toSyn (Finsupp.single f 1)) :
    Function.Surjective (actualCenterShearVertex MonomialOrder.degLex K f w htri) := by
  rintro ⟨a, ha⟩
  refine ⟨⟨a, ?_⟩, Subtype.ext rfl⟩
  simpa only [actualInitialVertices, actualInitialDiagram_map_centerShear MonomialOrder.degLex K f w htri]
    using ha

private theorem normalPivot_mem_iff (q f : Fin (n + 1)) (hqf : q ≤ f) (i : Fin (n + 1)) :
    normalPivotEquiv q f i ∈ normalPivotVariables q ↔ i ∈ normalPivotVariables q := by
  constructor
  · intro hi
    by_contra h
    have ht := normalPivotEquiv_tangent q f hqf i (lt_of_not_ge h)
    rw [ht] at hi
    exact h hi
  · intro hi
    by_contra h
    have hpi : normalPivotEquiv q f i < q := lt_of_not_ge h
    have hfix := normalPivotEquiv_tangent q f hqf (normalPivotEquiv q f i) hpi
    have heq : normalPivotEquiv q f i = i := (normalPivotEquiv q f).injective hfix
    rw [heq] at hpi
    exact (not_lt_of_ge hi) hpi

private theorem blowup_eq_of_normal_direction (A : Set (Fin (n + 1))) (e : Fin (n + 1))
    (b c : Fin (n + 1) → ℂ) (hbc : ∀ i ∈ A, i ≠ e → b i = c i) :
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

private theorem normalized_eq_of_normal_direction (A : Set (Fin (n + 1)))
    (e : Fin (n + 1)) (he : e ∈ A) (b c : Fin (n + 1) → ℂ)
    (hbc : ∀ i ∈ A, i ≠ e → b i = c i) (μ : ℕ)
    (F : MvPowerSeries (Fin (n + 1)) ℂ) (hF : F ∈ actualFormalCoordinateIdeal (n + 1) A ^ μ) :
    actualNormalizedFormalMember A e he b μ F hF = actualNormalizedFormalMember A e he c μ F hF := by
  apply actualNormalizedFormalMember_unique
  rw [← blowup_eq_of_normal_direction A e b c hbc]
  exact actualNormalizedFormalMember_spec A e he b μ F hF

private theorem strict_eq_of_normal_direction
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (A : Set (Fin (n + 1)))
    (e : Fin (n + 1)) (he : e ∈ A) (b c : Fin (n + 1) → ℂ)
    (hbc : ∀ i ∈ A, i ≠ e → b i = c i) :
    actualFormalStrictTransform K A e he b = actualFormalStrictTransform K A e he c := by
  rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal,
    actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
  unfold actualNormalizedOriginalMemberIdeal
  simp_rw [normalized_eq_of_normal_direction A e he b c hbc]

private theorem permute_degree (p : Fin (n + 1) ≃ Fin (n + 1)) (α : Fin (n + 1) →₀ ℕ) :
    normalExponentDegree (Finsupp.domCongr p α) = normalExponentDegree α := by
  simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    normalExponentDegree, ← Finsupp.degree_eq_sum] using Finsupp.degree_mapDomain p α

/-- The original actual normal HS equality supplies EVERY needed direction,
cylinder, adapted coordinate dictionary and target diagram internally. The
exact exceptional product retains each SAME original canonical numerator.
The scope is the specified derived linear shear plus normal-only promotion. -/
theorem exists_actual_normal_adapted_canonical_chart_of_hs_eq
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (q e : Fin (n + 1))
    (he : e ∈ normalPivotVariables q) (b : Fin (n + 1) → ℂ)
    (hD : ∀ i ∉ normalPivotVariables q, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal K)
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex K,
      actualReducedVertexSeries MonomialOrder.degLex K a ∈
        actualFormalCoordinateIdeal (n + 1) (normalPivotVariables q) ^
          Finsupp.weight (actualCoordinateWeight (normalPivotVariables q)) a.val)
    (hHS : ∀ ℓ, genuineFormalHilbertSamuelValue (n + 1)
      (actualFormalStrictTransform K (normalPivotVariables q) e he b) ℓ =
        genuineFormalHilbertSamuelValue (n + 1) K ℓ) :
    let v : Fin (n + 1) → ℂ := fun i =>
      actualPointUnitBasePoint e (actualNormalPointDirection (normalPivotVariables q) b) i
    ∃ (f : Fin (n + 1)) (_ : q ≤ f) (w : Fin (n + 1) → ℂ),
      v f ≠ 0 ∧ w = (fun i => v i / v f) ∧
      (∀ i < q, w i = 0) ∧
      (∀ i : Fin (n + 1), i ≠ f → w i ≠ 0 →
        MonomialOrder.degLex.toSyn (Finsupp.single i 1) <
          MonomialOrder.degLex.toSyn (Finsupp.single f 1)) ∧
      let KS := Ideal.map (actualFormalCenterShear Set.univ f w).toRingHom K
      let Kp := Ideal.map (normalPivotRename q f).toRingHom KS
      let Jp := normalZeroStrict Kp q
      ∃ (aP : actualInitialVertices MonomialOrder.degLex K → actualInitialVertices MonomialOrder.degLex Kp)
        (aJ : actualInitialVertices MonomialOrder.degLex K → actualInitialVertices MonomialOrder.degLex Jp),
        Function.Surjective aP ∧ Function.Surjective aJ ∧
        actualInitialDiagram MonomialOrder.degLex Kp =
          Finsupp.domCongr (normalPivotEquiv q f) '' actualInitialDiagram MonomialOrder.degLex K ∧
        actualInitialDiagram MonomialOrder.degLex Jp = actualInitialDiagram MonomialOrder.degLex Kp ∧
        (∀ a, (aP a).val = Finsupp.domCongr (normalPivotEquiv q f) a.val) ∧
        (∀ a, actualReducedVertexSeries MonomialOrder.degLex Kp (aP a) =
          normalPivotRename q f (actualFormalCenterShear Set.univ f w
            (actualReducedVertexSeries MonomialOrder.degLex K a))) ∧
        (∀ a, (aJ a).val = Finsupp.domCongr (normalPivotEquiv q f) a.val) ∧
        ∀ a, (MvPowerSeries.X q) ^ normalExponentDegree a.val *
          actualReducedVertexSeries MonomialOrder.degLex Jp (aJ a) =
            actualFormalBlowup (normalPivotVariables q) q (fun _ => 0)
              (normalPivotRename q f (actualFormalCenterShear Set.univ f w
                (actualReducedVertexSeries MonomialOrder.degLex K a))) := by
  let A := normalPivotVariables q
  let v : Fin (n + 1) → ℂ := fun i => actualPointUnitBasePoint e (actualNormalPointDirection A b) i
  have hve : v e = 1 := by simp only [v, actualPointUnitBasePoint_apply, if_true]
  have hv : ∃ i, v i ≠ 0 := ⟨e, by rw [hve]; exact one_ne_zero⟩
  have hvA (i : Fin (n + 1)) (hi : i ∉ A) : v i = 0 := by
    have hie : i ≠ e := by intro h; subst i; exact hi he
    simp only [v, actualPointUnitBasePoint_apply, if_neg hie, actualNormalPointDirection, if_neg hi]
  have hvb : ∀ i ∈ A, i ≠ e → v i = b i := by
    intro i hi hie
    simp only [v, actualPointUnitBasePoint_apply, if_neg hie, actualNormalPointDirection, if_pos hi]
  have hDir : ∀ F ∈ actualHomogeneousInitialIdeal K,
      (∑ i : Fin (n + 1), v i • MvPowerSeries.pderiv ℂ i F) ∈ actualHomogeneousInitialIdeal K :=
    actual_homogeneous_initial_normal_directional_stable_of_hs_eq K A e he b hD hV hHS
  obtain ⟨f, hvf, hmax, hvertices, _⟩ := exists_initial_direction_cylindrical_coordinate K v hv hDir
  have hfA : f ∈ A := by
    by_contra h
    exact hvf (hvA f h)
  have hqf : q ≤ f := hfA
  let w : Fin (n + 1) → ℂ := fun i => v i / v f
  have hwA : ∀ i ∉ A, w i = 0 := by intro i hi; simp only [w, hvA i hi, zero_div]
  have htri : ∀ i : Fin (n + 1), i ≠ f → w i ≠ 0 →
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
  let aS := actualCenterShearVertex MonomialOrder.degLex K f w htri
  have haS : Function.Surjective aS := centerShearVertex_surjective K f w htri
  have hVS : ∀ a : actualInitialVertices MonomialOrder.degLex KS,
      actualReducedVertexSeries MonomialOrder.degLex KS a ∈ actualFormalCoordinateIdeal (n + 1) A ^
        Finsupp.weight (actualCoordinateWeight A) a.val := by
    intro a
    obtain ⟨a, rfl⟩ := haS a
    rw [← actualFormalCenterShear_actualReducedVertexSeries MonomialOrder.degLex K f w htri hvertices a]
    have hm := (mem_coordinate_power_iff_centerShear A f hfA w _
      (actualReducedVertexSeries MonomialOrder.degLex K a)).mp (hV a)
    rwa [hS] at hm
  have hTS : ∀ a : actualInitialVertices MonomialOrder.degLex KS, ∀ i < q, a.val i = 0 := by
    intro a i hi
    obtain ⟨a, rfl⟩ := haS a
    change a.val i = 0
    have hiA : i ∉ A := not_le_of_gt hi
    exact actualInitialVertex_coordinate_eq_zero_of_pderiv_stable MonomialOrder.degLex
      (actualHomogeneousInitialIdeal K) i (hD i hiA) (actualHomogeneousInitialVertex K a)
  have hfS : ∀ a : actualInitialVertices MonomialOrder.degLex KS, a.val f = 0 := by
    intro a
    obtain ⟨a, rfl⟩ := haS a
    exact hvertices a
  have hSvariables : Ideal.map (actualFormalCenterShearAlgEquiv Set.univ f w).toRingEquiv.toRingHom
      (genuineFormalVariables (n + 1)) = genuineFormalVariables (n + 1) := by
    have hhom : (actualFormalCenterShearAlgEquiv Set.univ f w).toRingEquiv.toRingHom =
        (actualFormalCenterShear Set.univ f w).toRingHom := by
      apply RingHom.ext
      intro F
      rfl
    have hpoint : actualFormalCoordinateIdeal (n + 1) Set.univ = genuineFormalVariables (n + 1) := by
      simp only [actualFormalCoordinateIdeal, Set.image_univ, genuineFormalVariables]
    rw [hhom, ← hpoint]
    exact map_coordinateIdeal_centerShear Set.univ f (mem_univ f) w
  have hHSzero : ∀ ℓ, genuineFormalHilbertSamuelValue (n + 1)
      (actualFormalStrictTransform KS A f hfA (fun _ => 0)) ℓ =
        genuineFormalHilbertSamuelValue (n + 1) KS ℓ := by
    intro ℓ
    calc
      _ = genuineFormalHilbertSamuelValue (n + 1) (actualFormalStrictTransform K A f hfA w) ℓ := by
        dsimp only [KS]
        rw [← hS, actual_normal_strict_zero_map_centerShear K A f hfA w]
      _ = genuineFormalHilbertSamuelValue (n + 1) (actualFormalStrictTransform K A e he v) ℓ :=
        genuineFormalHilbertSamuelValue_normal_chart_transition K A e f he hfA v hve hvf ℓ
      _ = genuineFormalHilbertSamuelValue (n + 1) (actualFormalStrictTransform K A e he b) ℓ := by
        rw [strict_eq_of_normal_direction K A e he v b hvb]
      _ = genuineFormalHilbertSamuelValue (n + 1) K ℓ := hHS ℓ
      _ = genuineFormalHilbertSamuelValue (n + 1) KS ℓ :=
        genuineFormalHilbertSamuelValue_map_formalAlgEquiv
          (actualFormalCenterShearAlgEquiv Set.univ f w) hSvariables K ℓ
  let Kp := Ideal.map (normalPivotRename q f).toRingHom KS
  let aP : actualInitialVertices MonomialOrder.degLex K → actualInitialVertices MonomialOrder.degLex Kp :=
    fun a => normalPivotVertex KS q f hqf hTS hfS (aS a)
  have haP : Function.Surjective aP :=
    (normalPivotVertex_surjective KS q f hqf hTS hfS).comp haS
  have hVP := normalPivot_reduced_vertex_normal_powers KS q f hqf hTS hfS hVS
  have hTP : ∀ a : actualInitialVertices MonomialOrder.degLex Kp, ∀ i ∉ A, a.val i = 0 := by
    intro a i hi
    obtain ⟨a, rfl⟩ := normalPivotVertex_surjective KS q f hqf hTS hfS a
    exact normalPivotVertex_tangent KS q f hqf hTS hfS a i (lt_of_not_ge hi)
  have hDP := actual_tangent_initial_stability_of_pure_vertices_normal_powers Kp A hTP hVP
  have hpA : ∀ i, normalPivotEquiv q f i ∈ A ↔ i ∈ A := normalPivot_mem_iff q f hqf
  have hHSp : ∀ ℓ, genuineFormalHilbertSamuelValue (n + 1) (normalZeroStrict Kp q) ℓ =
      genuineFormalHilbertSamuelValue (n + 1) Kp ℓ := by
    have h := normal_strict_hs_eq_rename KS (normalPivotEquiv q f) A hpA f hfA
      (fun _ => 0) hHSzero
    simpa only [normalZeroStrict, Kp, normalPivotRename, A, normalPivotEquiv_pivot q f hqf] using h
  let aJ : actualInitialVertices MonomialOrder.degLex K →
      actualInitialVertices MonomialOrder.degLex (normalZeroStrict Kp q) :=
    fun a => normalZeroVertex Kp q hDP hVP hHSp (aP a)
  have haJ : Function.Surjective aJ := (normalZeroVertex_surjective Kp q hDP hVP hHSp).comp haP
  have hcanonP (a : actualInitialVertices MonomialOrder.degLex K) :
      actualReducedVertexSeries MonomialOrder.degLex Kp (aP a) =
        normalPivotRename q f (actualFormalCenterShear Set.univ f w
          (actualReducedVertexSeries MonomialOrder.degLex K a)) := by
    rw [← normalPivot_actualReducedVertexSeries KS q f hqf hTS hfS (aS a),
      ← actualFormalCenterShear_actualReducedVertexSeries MonomialOrder.degLex K f w htri hvertices a]
  refine ⟨f, hqf, w, hvf, rfl, (fun i hi => hwA i (not_le_of_gt hi)), htri, aP, aJ, haP, haJ, ?_,
    actualInitialDiagram_normal_zero_eq_of_hs_eq Kp q hDP hVP hHSp, (fun _ => rfl), hcanonP,
      (fun _ => rfl), ?_⟩
  · rw [actualInitialDiagram_normalPivot KS q f hqf hTS hfS,
      actualInitialDiagram_map_centerShear MonomialOrder.degLex K f w htri]
  · intro a
    have hcanonical := actual_normal_zero_normalized_eq_canonical Kp q hDP hVP hHSp (aP a)
    have hs := actualNormalizedFormalMember_spec A q (by change q ≤ q; exact le_rfl) (fun _ => 0) _
      (actualReducedVertexSeries MonomialOrder.degLex Kp (aP a)) (hVP (aP a))
    change (MvPowerSeries.X q) ^ Finsupp.weight (actualCoordinateWeight A) (aP a).val *
      actualNormalizedReducedFormalVertex MonomialOrder.degLex Kp A q (by change q ≤ q; exact le_rfl) (fun _ => 0) hVP (aP a) =
        actualFormalBlowup A q (fun _ => 0) (actualReducedVertexSeries MonomialOrder.degLex Kp (aP a)) at hs
    rw [actual_normal_vertex_mark_eq_degree Kp A hDP (aP a), hcanonical, hcanonP a] at hs
    have hdegree : normalExponentDegree (aP a).val = normalExponentDegree a.val :=
      permute_degree (normalPivotEquiv q f) a.val
    simpa only [hdegree] using hs

end
end Hironaka.HironakaActualNormalAdaptedDiagram
