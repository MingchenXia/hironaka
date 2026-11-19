import Hironaka.Resolution.HironakaActualRelativeStandardnessCoordinateJetSpanning
import Hironaka.Resolution.HironakaActualRelativeStandardnessBlockSupport
import Hironaka.Resolution.HironakaActualFormalMonomialBlowupReflection
import Hironaka.Resolution.HironakaActualCanonicalVertexDirectionalInvariance
import Hironaka.Resolution.HironakaActualPointNormalizedHomogeneous
import Hironaka.Resolution.HironakaActualConeEqualityDirectionalStability

/-!
# Actual normal-chart fibres produce the closed-point model and direction

The tangent scaling is a genuine whole monomial substitution. Its coefficient
embedding and the actual coordinate-power kernel prove a whole-series tangent
congruence, rather than checking only coordinate generators.

The final consumers internally supply the whole fibre dictionary and comparison
cylinder from source initial tangent stability and the SAME canonical centre
powers. They ask for actual strict/source HS equality, never target orders,
regular symbols, or jet bijectivity. Marked orders, the normal-only chart
transition, normal-block pivot promotion, and analytic histories are later steps.
-/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualRelativeStandardnessNormalPointBridge

noncomputable section

open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalMonomialBlowupReflection HironakaActualFormalStrictGenerators
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualCoefficientReducedStrictGenerators HironakaActualHomogeneousInitialHS
  HironakaActualTangentInitialVertices HironakaActualCanonicalVertexDirectionalInvariance
  HironakaActualPointExceptionalInitialForm HironakaActualPointDehomogenizedInitial
  HironakaActualPointExceptionalFibre HironakaActualPointExceptionalFibreRadial
  HironakaActualPointNormalizedHomogeneous HironakaActualPointInitialIdealInclusion
  HironakaActualRelativeStandardnessBlockSupport
  HironakaActualRelativeStandardnessCoordinateJetSpanning
  HironakaActualConeEqualityDirectionalStability HironakaActualPointUnitCoordinateChange
  HironakaActualUnshiftedInitialHSTransfer HironakaHolomorphicPointJets
  HironakaActualPointNormalizedBennett

variable {n : ℕ}

/-- The point direction agrees on the normal block and is zero on every tangent. -/
def actualNormalPointDirection (A : Set (Fin n)) (b : Fin n → ℂ) : Fin n → ℂ :=
  fun i => if i ∈ A then b i else 0

/-- This is only the genuine monomial substitution; its exceptional index need
not belong to its scaled subset. For e∈A it fixes the entire normal block. -/
def actualTangentScaling (A : Set (Fin n)) (e : Fin n) :
    MvPowerSeries (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  actualFormalBlowup Aᶜ e (fun _ => 0)

/-- The actual tangent and exceptional coordinate set used for the closed fibre. -/
def actualNormalPointFibreVariables (A : Set (Fin n)) (e : Fin n) : Set (Fin n) :=
  Aᶜ ∪ {e}

private theorem tangentScaling_X (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (i : Fin n) :
    actualTangentScaling A e (MvPowerSeries.X i) =
      if i ∈ A then MvPowerSeries.X i else MvPowerSeries.X e * MvPowerSeries.X i := by
  rw [actualTangentScaling, actualFormalBlowup_X]
  by_cases hi : i ∈ A
  · simp [actualFormalBlowupCoordinates, hi]
  · have hie : i ≠ e := by intro h; subst i; exact hi he
    simp [actualFormalBlowupCoordinates, hi, hie]

private theorem tangentScaling_exceptional (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) :
    actualTangentScaling A e (MvPowerSeries.X e) = MvPowerSeries.X e := by
  rw [tangentScaling_X A e he e, if_pos he]

private theorem tangentScaling_C (A : Set (Fin n)) (e : Fin n) (c : ℂ) :
    actualTangentScaling A e (MvPowerSeries.C c) = MvPowerSeries.C c :=
  (actualTangentScaling A e).commutes c

private theorem tangentScaling_normal_coordinate
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ) (i : Fin n) :
    actualTangentScaling A e (actualFormalBlowupCoordinates A e b i) =
      actualFormalBlowupCoordinates Set.univ e (actualNormalPointDirection A b) i := by
  by_cases hi : i ∈ A
  · by_cases hie : i = e
    · subst i
      simp only [actualFormalBlowupCoordinates, if_pos he,
        tangentScaling_exceptional A e he, Set.mem_univ, if_true]
    · simp only [actualFormalBlowupCoordinates, if_pos hi, if_neg hie,
        map_mul, map_add, tangentScaling_C, tangentScaling_exceptional A e he,
        tangentScaling_X A e he i, actualNormalPointDirection, Set.mem_univ, if_true]
  · have hie : i ≠ e := by intro h; subst i; exact hi he
    simp only [actualFormalBlowupCoordinates, if_neg hi, tangentScaling_X A e he i,
      actualNormalPointDirection, Set.mem_univ, if_true, if_neg hie, map_zero, zero_add]

/-- The genuine substitution composition theorem gives this equality on EVERY
formal series, with tangent direction zero internally. -/
theorem actualPointBlowup_eq_tangentScaling_normal
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalBlowup Set.univ e (actualNormalPointDirection A b) F =
      actualTangentScaling A e (actualFormalBlowup A e b F) := by
  let c := actualFormalBlowupCoordinates A e b
  let t := actualFormalBlowupCoordinates Aᶜ e (fun _ => 0)
  have hc := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (actualFormalBlowupCoordinates_constant_zero A e b)
  have ht := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (actualFormalBlowupCoordinates_constant_zero Aᶜ e (fun _ => 0))
  have hcoords : (fun i => MvPowerSeries.subst t (c i)) =
      actualFormalBlowupCoordinates Set.univ e (actualNormalPointDirection A b) := by
    funext i
    simpa only [actualTangentScaling, actualFormalBlowup, MvPowerSeries.substAlgHom_apply] using
      tangentScaling_normal_coordinate A e he b i
  simp only [actualTangentScaling, actualFormalBlowup, MvPowerSeries.substAlgHom_apply]
  rw [MvPowerSeries.subst_comp_subst_apply hc ht, hcoords]

private theorem point_power_of_coordinate_power
    (A : Set (Fin n)) (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ) :
    F ∈ actualFormalCoordinateIdeal n Set.univ ^ μ := by
  have hI : actualFormalCoordinateIdeal n A ≤ actualFormalCoordinateIdeal n Set.univ := by
    apply Ideal.span_le.mpr
    rintro G ⟨i, hi, rfl⟩
    exact Ideal.subset_span ⟨i, mem_univ i, rfl⟩
  exact (pow_le_pow_left' hI μ) hF

/-- Actual normalization uniqueness identifies the SAME numerator and mark. -/
theorem actualNormalizedPointMember_eq_tangentScaling_normal
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ) :
    actualNormalizedFormalMember Set.univ e (mem_univ e) (actualNormalPointDirection A b)
        μ F (point_power_of_coordinate_power A μ F hF) =
      actualTangentScaling A e (actualNormalizedFormalMember A e he b μ F hF) := by
  symm
  apply actualNormalizedFormalMember_unique
  calc
    _ = actualTangentScaling A e ((MvPowerSeries.X e) ^ μ *
        actualNormalizedFormalMember A e he b μ F hF) := by
      rw [map_mul, map_pow, tangentScaling_exceptional A e he]
    _ = actualTangentScaling A e (actualFormalBlowup A e b F) := by
      rw [actualNormalizedFormalMember_spec]
    _ = _ := (actualPointBlowup_eq_tangentScaling_normal A e he b F).symm

/-- The TRUE whole coefficient embedding and the TRUE coordinate ideal kernel
prove this congruence for an arbitrary entire formal series. -/
theorem actualTangentScaling_sub_mem_tangentIdeal
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (H : MvPowerSeries (Fin n) ℂ) :
    actualTangentScaling A e H - H ∈ actualFormalCoordinateIdeal n Aᶜ := by
  rw [← pow_one (actualFormalCoordinateIdeal n Aᶜ)]
  apply (mem_actualFormalCoordinateIdeal_pow_iff Aᶜ 1 _).mpr
  intro α hα
  have hweight : Finsupp.weight (actualCoordinateWeight Aᶜ) α = 0 := by omega
  have hset : Aᶜ \ {e} = Aᶜ := by
    ext i
    simp only [Set.mem_sdiff, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · exact And.left
    · intro hi
      refine ⟨hi, ?_⟩
      intro h
      subst i
      exact hi he
  have hExp : actualMonomialBlowupExponent Aᶜ e α = α := by
    change α + Finsupp.single e (Finsupp.weight (actualCoordinateWeight (Aᶜ \ {e})) α) = α
    rw [hset, hweight, Finsupp.single_zero, add_zero]
  have hcoeff := actualFormalBlowup_zero_coefficient Aᶜ e H α
  rw [hExp] at hcoeff
  rw [map_sub]
  exact sub_eq_zero.mpr hcoeff

private theorem tangentIdeal_le_fibre (A : Set (Fin n)) (e : Fin n) :
    actualFormalCoordinateIdeal n Aᶜ ≤
      actualFormalCoordinateIdeal n (actualNormalPointFibreVariables A e) := by
  apply Ideal.span_le.mpr
  rintro G ⟨i, hi, rfl⟩
  exact Ideal.subset_span ⟨i, Or.inl hi, rfl⟩

private theorem exceptionalIdeal_le_fibre (A : Set (Fin n)) (e : Fin n) :
    Ideal.span {(MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ)} ≤
      actualFormalCoordinateIdeal n (actualNormalPointFibreVariables A e) := by
  apply Ideal.span_le.mpr
  rintro G (rfl : G = MvPowerSeries.X e)
  exact Ideal.subset_span ⟨e, Or.inr (mem_singleton e), rfl⟩

/-- Every literal normal member has its true point leading polynomial modulo
all tangent coordinates and the actual exceptional coordinate. -/
theorem actualNormalizedNormalMember_congr_point_head_mod_fibre
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ) :
    actualNormalizedFormalMember A e he b μ F hF -
      (actualPointDehomogenization e (actualNormalPointDirection A b)
        (actualPointHomogeneousPolynomial μ F) : MvPowerSeries (Fin n) ℂ) ∈
      actualFormalCoordinateIdeal n (actualNormalPointFibreVariables A e) := by
  let H := actualNormalizedFormalMember A e he b μ F hF
  have hτ := actualTangentScaling_sub_mem_tangentIdeal A e he H
  have hPoint := actual_point_normalized_member_congr_dehomogenization e
    (actualNormalPointDirection A b) μ F (point_power_of_coordinate_power A μ F hF)
  rw [actualNormalizedPointMember_eq_tangentScaling_normal A e he b μ F hF] at hPoint
  have hsum := (actualFormalCoordinateIdeal n (actualNormalPointFibreVariables A e)).add_mem
    ((tangentIdeal_le_fibre A e) ((actualFormalCoordinateIdeal n Aᶜ).neg_mem hτ))
    ((exceptionalIdeal_le_fibre A e) hPoint)
  simp only [neg_sub] at hsum
  change H - actualTangentScaling A e H +
    (actualTangentScaling A e H -
      (actualPointDehomogenization e (actualNormalPointDirection A b)
        (actualPointHomogeneousPolynomial μ F) : MvPowerSeries (Fin n) ℂ)) ∈
      actualFormalCoordinateIdeal n (actualNormalPointFibreVariables A e) at hsum
  simpa only [neg_sub, sub_add_sub_cancel] using hsum

private theorem point_weight_eq_degree (α : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight Set.univ) α = normalExponentDegree α := by
  simp only [Finsupp.weight_eq_sum, actualCoordinateWeight, Set.mem_univ,
    if_true, smul_eq_mul, mul_one, normalExponentDegree]

private theorem vertex_normal_mark_eq_point_mark
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n))
    (hD : ∀ i ∉ A, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal K)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    Finsupp.weight (actualCoordinateWeight A) a.val =
      Finsupp.weight (actualCoordinateWeight Set.univ) a.val := by
  have hz (i : Fin n) (hi : i ∉ A) : a.val i = 0 :=
    actualInitialVertex_coordinate_eq_zero_of_pderiv_stable MonomialOrder.degLex
      (actualHomogeneousInitialIdeal K) i (hD i hi) (actualHomogeneousInitialVertex K a)
  rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ A
  · simp only [actualCoordinateWeight, if_pos hi, Set.mem_univ, if_true]
  · simp only [actualCoordinateWeight, if_neg hi, Set.mem_univ, if_true, hz i hi, zero_smul]

private theorem span_range_sup_eq_of_sub_mem {ι R : Type*} [CommRing R]
    (F G : ι → R) (E : Ideal R) (h : ∀ i, F i - G i ∈ E) :
    Ideal.span (range F) ⊔ E = Ideal.span (range G) ⊔ E := by
  apply le_antisymm
  · apply sup_le _ le_sup_right
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    have hm := (Ideal.span (range G) ⊔ E).add_mem
      (Ideal.mem_sup_right (h i)) (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
    change F i ∈ Ideal.span (range G) ⊔ E
    simpa only [sub_add_cancel] using hm
  · apply sup_le _ le_sup_right
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    have hneg : G i - F i ∈ E := by simpa only [neg_sub] using E.neg_mem (h i)
    have hm := (Ideal.span (range F) ⊔ E).add_mem
      (Ideal.mem_sup_right hneg) (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
    change G i ∈ Ideal.span (range F) ⊔ E
    simpa only [sub_add_cancel] using hm

/-- Source canonical normal powers and source initial tangent stability PRODUCE
the whole actual fibre identity; no such identity is supplied as a premise. -/
theorem actual_normal_strict_fibre_eq_dehomogenized_point_model
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hD : ∀ i ∉ A, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal K)
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex K,
      actualReducedVertexSeries MonomialOrder.degLex K a ∈ actualFormalCoordinateIdeal n A ^
        Finsupp.weight (actualCoordinateWeight A) a.val) :
    actualFormalStrictTransform K A e he b ⊔
        actualFormalCoordinateIdeal n (actualNormalPointFibreVariables A e) =
      actualDehomogenizedPointInitialConeIdeal K e (actualNormalPointDirection A b) ⊔
        actualFormalCoordinateIdeal n (actualNormalPointFibreVariables A e) := by
  let E := actualFormalCoordinateIdeal n (actualNormalPointFibreVariables A e)
  let D := actualCanonicalPointDehomogenizedIdeal K e (actualNormalPointDirection A b)
  have hGen (a : actualInitialVertices MonomialOrder.degLex K) :
      actualNormalizedReducedFormalVertex MonomialOrder.degLex K A e he b hV a -
        (actualPointDehomogenization e (actualNormalPointDirection A b)
          (actualPointHomogeneousPolynomial
            (Finsupp.weight (actualCoordinateWeight Set.univ) a.val)
            (actualReducedVertexSeries MonomialOrder.degLex K a)) :
              MvPowerSeries (Fin n) ℂ) ∈ E := by
    have h := actualNormalizedNormalMember_congr_point_head_mod_fibre A e he b
      (Finsupp.weight (actualCoordinateWeight A) a.val)
      (actualReducedVertexSeries MonomialOrder.degLex K a) (hV a)
    have hHead := congrArg (fun μ =>
      (actualPointDehomogenization e (actualNormalPointDirection A b)
        (actualPointHomogeneousPolynomial μ (actualReducedVertexSeries MonomialOrder.degLex K a)) :
          MvPowerSeries (Fin n) ℂ)) (vertex_normal_mark_eq_point_mark K A hD a)
    rw [hHead] at h
    exact h
  have hSpan : actualFormalStrictTransform K A e he b ⊔ E = D ⊔ E := by
    rw [actualFormalStrictTransform_eq_reduced_vertex_span MonomialOrder.degLex K A e he b hV]
    exact span_range_sup_eq_of_sub_mem _ _ E hGen
  have hQ := actual_point_initial_cone_exceptional_fibre_eq_canonical_reduced
    K e (actualNormalPointDirection A b)
  have hExc : Ideal.span {(MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ)} ≤ E :=
    exceptionalIdeal_le_fibre A e
  have hQE : actualDehomogenizedPointInitialConeIdeal K e (actualNormalPointDirection A b) ⊔ E =
      D ⊔ E := by
    calc
      _ = (actualDehomogenizedPointInitialConeIdeal K e (actualNormalPointDirection A b) ⊔
          Ideal.span {MvPowerSeries.X e}) ⊔ E := by
        rw [sup_assoc, sup_eq_right.mpr hExc]
      _ = (D ⊔ Ideal.span {MvPowerSeries.X e}) ⊔ E := by rw [hQ]
      _ = D ⊔ E := by rw [sup_assoc, sup_eq_right.mpr hExc]
  exact hSpan.trans hQE.symm

/-- Exceptional projection upgrades the existing entire fibre equality to a
literal canonical-generator equality for the entire comparison cone. -/
theorem actualDehomogenizedPointInitialConeIdeal_eq_canonical
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ) :
    actualDehomogenizedPointInitialConeIdeal K e b = actualCanonicalPointDehomogenizedIdeal K e b := by
  let π := actualPointExceptionalProjection e
  have hmap : Ideal.map π.toRingHom (actualCanonicalPointDehomogenizedIdeal K e b) =
      actualCanonicalPointDehomogenizedIdeal K e b := by
    rw [actualCanonicalPointDehomogenizedIdeal, Ideal.map_span, ← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext a
    exact actualPointExceptionalProjection_dehomogenization e b _
  have hzero : Ideal.map π.toRingHom
      (Ideal.span {(MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ)}) = ⊥ := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {actualPointExceptionalProjection e (MvPowerSeries.X e)} = ⊥
    rw [actualPointExceptionalProjection_X, if_pos rfl, Ideal.span_singleton_zero]
  have h := congrArg (Ideal.map π.toRingHom)
    (actual_point_initial_cone_exceptional_fibre_eq_canonical_reduced K e b)
  simp only [Ideal.map_sup, hmap, hzero, sup_bot_eq] at h
  change Ideal.map (actualPointExceptionalProjection e).toRingHom
    (actualDehomogenizedPointInitialConeIdeal K e b) = _ at h
  simpa only [map_actualDehomogenizedPointInitialConeIdeal_projection] using h

private theorem homogeneous_polynomial_mem_point_power
    (P : MvPolynomial (Fin n) ℂ) (μ : ℕ) (hP : P.IsHomogeneous μ) :
    (P : MvPowerSeries (Fin n) ℂ) ∈ actualFormalCoordinateIdeal n Set.univ ^ μ := by
  apply (mem_actualFormalCoordinateIdeal_pow_iff Set.univ μ _).mpr
  intro α hα
  by_contra hne
  have hcoeff : MvPolynomial.coeff α P ≠ 0 := by simpa only [MvPolynomial.coeff_coe] using hne
  have hdegree : Finsupp.degree α = μ := by
    simpa only [Finsupp.weight_eq_sum, Pi.one_apply, smul_eq_mul, mul_one,
      Finsupp.degree_eq_sum] using hP hcoeff
  have hlt : Finsupp.degree α < μ := by
    simpa only [point_weight_eq_degree, normalExponentDegree, Finsupp.degree_eq_sum] using hα
  omega

private theorem pderiv_dehomogenization_zero_of_source
    (e i : Fin n) (hie : i ≠ e) (b : Fin n → ℂ) (hbi : b i = 0)
    (P : MvPolynomial (Fin n) ℂ) (μ : ℕ) (hP : P.IsHomogeneous μ)
    (hD : MvPowerSeries.pderiv ℂ i (P : MvPowerSeries (Fin n) ℂ) = 0) :
    MvPowerSeries.pderiv ℂ i
      (actualPointDehomogenization e b P : MvPowerSeries (Fin n) ℂ) = 0 := by
  have hPow := homogeneous_polynomial_mem_point_power P μ hP
  have hNorm : actualNormalizedFormalMember Set.univ e (mem_univ e) b μ
      (P : MvPowerSeries (Fin n) ℂ) hPow =
        (actualPointDehomogenization e b P : MvPowerSeries (Fin n) ℂ) := by
    symm
    apply actualNormalizedFormalMember_unique
    exact (actualFormalBlowup_homogeneous_polynomial e b P μ hP).symm
  have hSupp : ∀ α, 0 < α i → MvPowerSeries.coeff α
      (actualNormalizedFormalMember Set.univ e (mem_univ e) b μ
        (P : MvPowerSeries (Fin n) ℂ) hPow) = 0 := by
    apply actualNormalizedFormalMember_forbidden_block_support Set.univ {i} e (mem_univ e) b
      (fun _ _ => mem_univ _) (by simpa only [Set.mem_singleton_iff] using hie.symm)
      (by intro j hj; have heq : j = i := hj; subst j; exact hbi)
      μ (P : MvPowerSeries (Fin n) ℂ) hPow (fun α => 0 < α i)
    · intro α β h
      rw [h i (mem_singleton i)]
    · intro α hα
      exact coeff_eq_zero_of_pderiv_eq_zero_of_pos i _ hD α hα
  rw [hNorm] at hSupp
  apply MvPowerSeries.ext
  intro α
  rw [MvPowerSeries.coeff_pderiv, map_zero,
    hSupp (α + Finsupp.single i 1) (by simp only [Finsupp.add_apply, Finsupp.single_eq_same]; omega),
    zero_mul]

private theorem pderiv_mem_span_of_generators_zero (S : Set (MvPowerSeries (Fin n) ℂ))
    (i : Fin n) (hS : ∀ F ∈ S, MvPowerSeries.pderiv ℂ i F = 0) :
    ∀ F ∈ Ideal.span S, MvPowerSeries.pderiv ℂ i F ∈ Ideal.span S := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF => rw [hS F hF]; exact Ideal.zero_mem _
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add F G _ _ hF hG => simpa only [map_add] using (Ideal.span S).add_mem hF hG
  | smul C F hF ih =>
      change MvPowerSeries.pderiv ℂ i (C * F) ∈ Ideal.span S
      rw [Derivation.leibniz]
      exact (Ideal.span S).add_mem ((Ideal.span S).mul_mem_left C ih)
        ((Ideal.span S).mul_mem_right _ hF)

/-- Source initial tangent stability PRODUCES the entire comparison cylinder,
including the exceptional coordinate, without a target regularity premise. -/
theorem actual_dehomogenized_point_model_coordinate_cylinder_of_tangent_initial_stability
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hD : ∀ i ∉ A, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal K) :
    actualCoordinateDiagramCylinder
      (actualDehomogenizedPointInitialConeIdeal K e (actualNormalPointDirection A b))
      (actualNormalPointFibreVariables A e) := by
  apply actualCoordinateDiagramCylinder_of_partial_stability
  intro i hi F hF
  rw [actualDehomogenizedPointInitialConeIdeal_eq_canonical,
    actualCanonicalPointDehomogenizedIdeal] at hF ⊢
  apply pderiv_mem_span_of_generators_zero _ i ?_ F hF
  rintro H ⟨a, rfl⟩
  rcases hi with hi | hi
  · have hiA : i ∉ A := hi
    have hie : i ≠ e := by intro h; subst i; exact hiA he
    have hpartial : MvPowerSeries.pderiv ℂ i
        (actualPointHomogeneousPolynomial
          (Finsupp.weight (actualCoordinateWeight Set.univ) a.val)
          (actualReducedVertexSeries MonomialOrder.degLex K a) : MvPowerSeries (Fin n) ℂ) = 0 := by
      rw [actualPointHomogeneousPolynomial_coe, point_weight_eq_degree]
      exact pderiv_homogeneousComponent_actualReducedVertexSeries_eq_zero_of_stable K i (hD i hiA) a
    exact pderiv_dehomogenization_zero_of_source e i hie (actualNormalPointDirection A b)
      (by simp only [actualNormalPointDirection, if_neg hiA]) _ _
      (actualPointHomogeneousPolynomial_isHomogeneous _ _) hpartial
  · have hie : i = e := hi
    subst i
    exact pderiv_actualPointDehomogenization_eq_zero e (actualNormalPointDirection A b) _

/-- Only original whole source data and true normal strict/source HS equality
are supplied; fibre, cylinder and the SAME actual jet bijectivity are produced. -/
theorem actual_normal_strict_model_jetMap_bijective_of_hs_eq
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hD : ∀ i ∉ A, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal K)
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex K,
      actualReducedVertexSeries MonomialOrder.degLex K a ∈ actualFormalCoordinateIdeal n A ^
        Finsupp.weight (actualCoordinateWeight A) a.val)
    (hHS : ∀ ℓ : ℕ, genuineFormalHilbertSamuelValue n (actualFormalStrictTransform K A e he b) ℓ =
      genuineFormalHilbertSamuelValue n K ℓ) :
    ∀ ℓ : ℕ, Function.Bijective (actualStandardModelJetMap (actualFormalStrictTransform K A e he b)
      (actualDehomogenizedPointInitialConeIdeal K e (actualNormalPointDirection A b)) (ℓ + 1)) := by
  intro ℓ
  exact actualDehomogenizedModelJetMap_bijective_of_source_hs_eq K _ e
    (actualNormalPointDirection A b) (actualNormalPointFibreVariables A e)
    (actual_normal_strict_fibre_eq_dehomogenized_point_model K A e he b hD hV)
    (actual_dehomogenized_point_model_coordinate_cylinder_of_tangent_initial_stability K A e he b hD)
    ℓ (hHS ℓ)

/-- The actual normal direction's whole source initial stability is now an
output of true normal strict/source HS equality, not a new geometric premise. -/
theorem actual_homogeneous_initial_normal_directional_stable_of_hs_eq
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hD : ∀ i ∉ A, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal K)
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex K,
      actualReducedVertexSeries MonomialOrder.degLex K a ∈ actualFormalCoordinateIdeal n A ^
        Finsupp.weight (actualCoordinateWeight A) a.val)
    (hHS : ∀ ℓ : ℕ, genuineFormalHilbertSamuelValue n (actualFormalStrictTransform K A e he b) ℓ =
      genuineFormalHilbertSamuelValue n K ℓ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualHomogeneousInitialIdeal K) :
    (∑ i : Fin n, actualPointUnitBasePoint e (actualNormalPointDirection A b) i •
      MvPowerSeries.pderiv ℂ i F) ∈ actualHomogeneousInitialIdeal K := by
  apply actual_homogeneous_initial_directional_stable_of_translated_hs_eq K
    (actualPointUnitBasePoint e (actualNormalPointDirection A b)) ?_ F hF
  intro ℓ
  rw [← hilbertSamuelValue_actualDehomogenizedInitialIdeal_eq_translated K e
      (actualNormalPointDirection A b) ℓ,
    hilbertSamuelValue_eq_actual_unshifted_formal_extension,
    actualDehomogenizedInitialIdeal_formal_extension_whole_cone]
  have hmodel := genuineFormalHilbertSamuelValue_dehomogenizedModel_eq_of_source_hs_eq K _ e
    (actualNormalPointDirection A b) (actualNormalPointFibreVariables A e)
    (actual_normal_strict_fibre_eq_dehomogenized_point_model K A e he b hD hV)
    (actual_dehomogenized_point_model_coordinate_cylinder_of_tangent_initial_stability K A e he b hD)
    ℓ (hHS ℓ)
  exact hmodel.symm.trans (hHS ℓ)

end

end Hironaka.HironakaActualRelativeStandardnessNormalPointBridge
