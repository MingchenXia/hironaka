import Hironaka.Resolution.HironakaActualRelativeStandardnessNormalCorrection
import Hironaka.Resolution.HironakaActualNearbyTangentParameters
import Hironaka.Resolution.HironakaActualTangentInitialVertices
import Hironaka.Resolution.HironakaActualAnalyticVertexBasis
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor
import Hironaka.Resolution.HironakaActualAnalyticFormalNormalPowers
import Hironaka.Resolution.HironakaActualCanonicalCentreCompatibility

/-!
# Corrected original analytic vertices and the same canonical normal powers

Free actual normal truncations produce corrections inside the original ideal.
Pure normal coefficients survive these corrections, so the corrected vertices
form a compatible monic family for the unchanged formal ideal. Canonical formal
division then transfers its powers to the same reduced vertex series.
-/

set_option autoImplicit false

namespace Hironaka.HironakaActualRelativeStandardnessAnalyticFamily

noncomputable section

open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalFibreHilbertSamuel HironakaActualNearbyTangentParameters
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticBlowupTaylor
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalInitialDiagram
  HironakaActualFormalStandardMonomialHS HironakaActualOriginalFormalTaylor
  HironakaActualOriginalFormalHSTransfer
  HironakaActualAnalyticVertexBasis HironakaActualCoordinateSymbolRegularity
  HironakaActualHomogeneousInitialHS HironakaActualTangentInitialVertices
  HironakaActualRelativeStandardnessNormalCorrection
  HironakaActualAnalyticFormalNormalPowers HironakaActualReducedBasisDivision
  HironakaActualReducedFormalStandardBasis HironakaActualCanonicalCentreCompatibility

theorem originalBaseMaximalIdeal_eq_tangent_coordinate_ideal (d t : ℕ) :
    originalBaseMaximalIdeal d t =
      actualAnalyticCoordinateIdeal (Set.range (Fin.castAdd t : Fin d → Fin (d+t))) := by
  simpa only [actualAnalyticCoordinateIdeal, ← Set.range_comp, Function.comp_def] using
    originalBaseMaximalIdeal_eq_span_tangent_coordinates d t

private theorem tangent_not_mem_normal_variables (d t : ℕ) (i : Fin d) :
    i.castAdd t ∉ actualTangentCentreVariables d t := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change d + j.val = i.val at hv
  omega

private theorem normal_not_mem_tangent_variables (d t : ℕ) (j : Fin t) :
    j.natAdd d ∉ Set.range (Fin.castAdd t : Fin d → Fin (d+t)) := by
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  change i.val = d + j.val at hv
  omega

theorem actual_normal_coordinate_weight_eq_sum (d t : ℕ) (a : Fin (d+t) →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a =
      ∑ j : Fin t, a (j.natAdd d) := by
  classical
  rw [Finsupp.weight_eq_sum, Fin.sum_univ_add]
  have hz : (∑ i : Fin d, a (i.castAdd t) •
      actualCoordinateWeight (actualTangentCentreVariables d t) (i.castAdd t)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [actualCoordinateWeight, if_neg (tangent_not_mem_normal_variables d t i),
      smul_zero]
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.natAdd d ∈ actualTangentCentreVariables d t := ⟨j, rfl⟩
  simp only [actualCoordinateWeight, if_pos hj, smul_eq_mul, mul_one]

theorem actual_normal_weight_eq_degree_of_tangent_zero (d t : ℕ)
    (a : Fin (d+t) →₀ ℕ) (ha : ∀ i : Fin d, a (i.castAdd t) = 0) :
    Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a =
      normalExponentDegree a := by
  rw [actual_normal_coordinate_weight_eq_sum, normalExponentDegree, Fin.sum_univ_add]
  have hz : (∑ i : Fin d, a (i.castAdd t)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact ha i
  rw [hz, zero_add]

theorem tangent_zero_of_degree_le_normal_weight (d t : ℕ)
    (a : Fin (d+t) →₀ ℕ) (q : ℕ) (hdeg : normalExponentDegree a ≤ q)
    (hw : q ≤ Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a)
    (i : Fin d) : a (i.castAdd t) = 0 := by
  have hsum : normalExponentDegree a = (∑ j : Fin d, a (j.castAdd t)) +
      Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a := by
    rw [actual_normal_coordinate_weight_eq_sum, normalExponentDegree, Fin.sum_univ_add]
  have hzero : (∑ j : Fin d, a (j.castAdd t)) = 0 := by omega
  have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
    Nat.zero_le (a (j.castAdd t))) (Finset.mem_univ i)
  omega

/-- Subtracting a base-maximal germ preserves every pure normal Taylor coefficient. -/
theorem coeff_eq_of_sub_mem_originalBaseMaximalIdeal (d t : ℕ)
    (g g' : HolGerm (ComplexModel (d+t)))
    (hgg' : g-g' ∈ originalBaseMaximalIdeal d t)
    (a : Fin (d+t) →₀ ℕ) (ha : ∀ i : Fin d, a (i.castAdd t)=0) :
    MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom (d+t) g) =
      MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom (d+t) g') := by
  classical
  let A : Set (Fin (d+t)) := Set.range (Fin.castAdd t : Fin d → Fin (d+t))
  have hTaylor : actualUnshiftedTaylorAlgHom (d+t) (g-g') ∈
      actualFormalCoordinateIdeal (d+t) A ^ 1 := by
    rw [pow_one]
    have hm := Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom (d+t)).toRingHom hgg'
    rwa [originalBaseMaximalIdeal_eq_tangent_coordinate_ideal,
      map_actualAnalyticCoordinateIdeal_taylor] at hm
  have hw : Finsupp.weight (actualCoordinateWeight A) a = 0 := by
    rw [Finsupp.weight_eq_sum, Fin.sum_univ_add]
    apply add_eq_zero.mpr
    constructor
    · apply Finset.sum_eq_zero
      intro i _
      rw [ha i, zero_smul]
    · apply Finset.sum_eq_zero
      intro j _
      simp only [A, actualCoordinateWeight,
        if_neg (normal_not_mem_tangent_variables d t j), smul_zero]
  have hz := (mem_actualFormalCoordinateIdeal_pow_iff A 1 _).mp hTaylor a (by omega)
  simpa only [map_sub, sub_eq_zero] using hz

private theorem unshiftedTaylor_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

theorem exists_unshifted_original_analytic_vertex_basis (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) :
    ∃ G : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) → HolGerm (ComplexModel n),
      ∀ a, G a ∈ I ∧ ∃ hne : actualUnshiftedTaylorAlgHom n (G a) ≠ 0,
        actualInitialExponent MonomialOrder.degLex (actualUnshiftedTaylorAlgHom n (G a)) hne =
          a.val ∧ MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom n (G a)) = 1 := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ I : Ideal (HolGerm (ComplexModel m)),
      ∃ G : actualInitialVertices MonomialOrder.degLex (Ideal.map f.toRingHom I) →
          HolGerm (ComplexModel m),
        ∀ a, G a ∈ I ∧ ∃ hne : f (G a) ≠ 0,
          actualInitialExponent MonomialOrder.degLex (f (G a)) hne = a.val ∧
            MvPowerSeries.coeff a.val (f (G a)) = 1
  have hs : P (0+n) (originalTaylorAlgHom n) := by
    intro J
    obtain ⟨G, hG, _⟩ := exists_actual_original_analytic_vertex_basis n J
    exact ⟨G, hG⟩
  exact unshiftedTaylor_property n P hs I

/-- Free entire normal truncations and genuine tangent stability produce a compatible
monic family for the same original formal ideal. -/
theorem exists_original_compatible_monic_vertex_family (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hD : ∀ i : Fin d, ∀ F ∈ actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I),
      MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈ actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I))
    (hfree : ∀ q : ℕ, letI := tangentAlgebra d t
      Module.Free (HolGerm (ComplexModel d))
        (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q))) :
    ∃ B : ActualMonicVertexFamily MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I),
      ∀ a, familyVertexSeries MonomialOrder.degLex _ B a ∈
        actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t) ^
          Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val := by
  classical
  let K := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I
  obtain ⟨G, hG⟩ := exists_unshifted_original_analytic_vertex_basis (d+t) I
  have hCorrection (a : actualInitialVertices MonomialOrder.degLex K) :
      ∃ g' ∈ I, g' ∈ normalIdeal d t ^ normalExponentDegree a.val ∧
        G a - g' ∈ originalBaseMaximalIdeal d t := by
    obtain ⟨hGaI, hne, hinit, _⟩ := hG a
    have hformal : actualUnshiftedTaylorAlgHom (d+t) (G a) ∈
        genuineFormalVariables (d+t) ^ normalExponentDegree a.val := by
      apply (mem_formal_variables_pow_iff_degree_initialExponent _ hne _).mpr
      rw [hinit]
    have hgpow := (mem_original_thickening_iff_unshifted_taylor (d+t) (⊥ : Ideal _)
      (normalExponentDegree a.val) (G a)).mpr
      (by simpa only [Ideal.map_bot, bot_sup_eq] using hformal)
    simp only [bot_sup_eq] at hgpow
    exact exists_original_normal_power_correction d t I _ (hfree _) (G a) hGaI hgpow
  choose G' hG'I hG'N hGG' using hCorrection
  have hPure (a : actualInitialVertices MonomialOrder.degLex K) (i : Fin d) :
      a.val (i.castAdd t) = 0 := actualInitialVertex_tangent_eq_zero d t K hD a i
  have hCoeff (a : actualInitialVertices MonomialOrder.degLex K) :
      MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom (d+t) (G' a)) = 1 := by
    rw [← coeff_eq_of_sub_mem_originalBaseMaximalIdeal d t (G a) (G' a)
      (hGG' a) a.val (hPure a)]
    exact (hG a).2.choose_spec.2
  have hLower (a : actualInitialVertices MonomialOrder.degLex K) (b : Fin (d+t) →₀ ℕ)
      (hb : MonomialOrder.degLex.toSyn b < MonomialOrder.degLex.toSyn a.val) :
      MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom (d+t) (G' a)) = 0 := by
    let w := Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) b
    have hNormal := (mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow d t
      (normalExponentDegree a.val) (G' a)).mp (hG'N a)
    by_cases hw : w < normalExponentDegree a.val
    · exact (mem_actualFormalCoordinateIdeal_pow_iff _ _ _).mp hNormal b hw
    · have hdeg := actual_degree_le_of_deglex_lt b a.val hb
      have hbPure (i : Fin d) : b (i.castAdd t) = 0 := by
        exact tangent_zero_of_degree_le_normal_weight d t b _ hdeg (Nat.le_of_not_gt hw) i
      rw [← coeff_eq_of_sub_mem_originalBaseMaximalIdeal d t (G a) (G' a)
        (hGG' a) b hbPure]
      obtain ⟨_, hne, hinit, _⟩ := hG a
      exact coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex _ hne b
        (by rwa [hinit])
  let B : ActualMonicVertexFamily MonomialOrder.degLex K :=
    { series := fun a => actualUnshiftedTaylorAlgHom (d+t) (G' a)
      mem := fun a => Ideal.mem_map_of_mem _ (hG'I a)
      monic := hCoeff
      lower := hLower }
  refine ⟨B, ?_⟩
  intro a
  change actualUnshiftedTaylorAlgHom (d+t) (G' a) ∈ _
  rw [actual_normal_weight_eq_degree_of_tangent_zero d t a.val (hPure a)]
  exact (mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow d t _ (G' a)).mp (hG'N a)

/-- The same canonical reduced vertices inherit the actual centre normal powers. -/
theorem original_actualReducedVertexSeries_mem_normal_power (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hD : ∀ i : Fin d, ∀ F ∈ actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I),
      MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈ actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I))
    (hfree : ∀ q : ℕ, letI := tangentAlgebra d t
      Module.Free (HolGerm (ComplexModel d))
        (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q)))
    (a : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)) :
    actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a ∈
      actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t) ^
        Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val := by
  obtain ⟨B, hB⟩ := exists_original_compatible_monic_vertex_family d t I hD hfree
  exact actualReducedVertexSeries_mem_coordinate_power_of_family
    MonomialOrder.degLex _ B (actualTangentCentreVariables d t) hB a

end

end Hironaka.HironakaActualRelativeStandardnessAnalyticFamily
